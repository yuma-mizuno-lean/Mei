/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.LinearAlgebra.ModuleFiltration.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Modules supported on a translate of a positive monoid

For a grading `ℳ`, a positive monoid `P`, and an ambient degree `p`,
`shiftedSubmodule ℳ P p` is the sum of the pieces `ℳ (p + n)` for `n ∈ P`.
Its relative-degree filtration counts the degree of `n`, rather than that of `p + n`.
Thus its order-zero quotient retains the original piece `ℳ p`, even when `p` has
negative degree. These filtered modules provide coefficient spaces on which positive
degree operators can act.

The filtration restricts `Mei.DirectSum.degreeTail`; its membership and separatedness
use the ambient homogeneous decomposition. The relative decomposition uses
`TauCeti.DirectSum.Decomposition.restrict` and `DirectSum.map_decompose_shift`.
No freeness or finiteness of the pieces is required.
-/

public section

noncomputable section

namespace Mei

variable {Γ R M : Type*} [AddCommGroup Γ] [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : Γ → Submodule R M) (P : AddSubmonoid Γ) (p : Γ)

/-- The submodule supported in the translate `p + P`. -/
def shiftedSubmodule : Submodule R M := ⨆ n : P, ℳ (p + n)

/-- The shifted submodule is the sum of its allowed homogeneous pieces. -/
theorem shiftedSubmodule_def :
    shiftedSubmodule ℳ P p = ⨆ n : P, ℳ (p + n) := (rfl)

/-- Every allowed homogeneous piece lies in the shifted module. -/
theorem le_shiftedSubmodule {n : Γ} (hn : n ∈ P) : ℳ (p + n) ≤ shiftedSubmodule ℳ P p :=
  le_iSup (fun n : P => ℳ (p + n)) ⟨n, hn⟩

/-- Include an allowed homogeneous coefficient in the shifted module. -/
def shiftedInclusion (n : P) : ℳ (p + n) →ₗ[R] shiftedSubmodule ℳ P p :=
  Submodule.inclusion (le_shiftedSubmodule ℳ P p n.property)

@[simp]
theorem coe_shiftedInclusion (n : P) (x : ℳ (p + n)) :
    (shiftedInclusion ℳ P p n x : M) = x := (rfl)

variable [DecidableEq Γ] [DirectSum.Decomposition ℳ]

/-- The ambient components outside `p + P` vanish exactly on the shifted module. -/
theorem mem_shiftedSubmodule_iff {x : M} :
    x ∈ shiftedSubmodule ℳ P p ↔
      ∀ q, q - p ∉ P → (DirectSum.decompose ℳ x q : M) = 0 := by
  classical
  constructor
  · intro hx q hq
    refine Submodule.iSup_induction _
      (motive := fun x => (DirectSum.decompose ℳ x q : M) = 0) hx
      (fun n x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
    apply DirectSum.decompose_of_mem_ne ℳ hx
    intro he
    apply hq
    simpa only [← he, add_sub_cancel_left] using n.property
  · intro hx
    rw [← DirectSum.sum_support_decompose ℳ x]
    apply Submodule.sum_mem
    intro q _
    by_cases hq : q - p ∈ P
    · have he : p + (q - p) = q := by abel
      apply le_shiftedSubmodule ℳ P p hq
      simpa only [he] using (DirectSum.decompose ℳ x q).property
    · rw [hx q hq]
      exact Submodule.zero_mem _

/-- The shifted submodule is stable under every ambient homogeneous projection. -/
theorem shiftedSubmodule_isHomogeneous :
    DirectSum.SetLike.IsHomogeneous ℳ (shiftedSubmodule ℳ P p) := by
  intro q x hx
  by_cases hq : q - p ∈ P
  · have he : p + (q - p) = q := by abel
    apply le_shiftedSubmodule ℳ P p hq
    simpa only [he] using (DirectSum.decompose ℳ x q).property
  · rw [(mem_shiftedSubmodule_iff ℳ P p).mp hx q hq]
    exact Submodule.zero_mem _

/-- Relative degree `n` is ambient degree `p + n` in the shifted submodule. -/
def shiftedGrading (n : Γ) : Submodule R (shiftedSubmodule ℳ P p) :=
  (ℳ (p + n)).comap (shiftedSubmodule ℳ P p).subtype

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] in
/-- Each relative homogeneous piece is the inverse image of its ambient piece. -/
theorem shiftedGrading_def (n : Γ) :
    shiftedGrading ℳ P p n =
      (ℳ (p + n)).comap (shiftedSubmodule ℳ P p).subtype := (rfl)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] in
/-- Relative homogeneity is ambient homogeneity after adding `p`. -/
@[simp]
theorem mem_shiftedGrading {n : Γ} {x : shiftedSubmodule ℳ P p} :
    x ∈ shiftedGrading ℳ P p n ↔ (x : M) ∈ ℳ (p + n) := (Iff.rfl)

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ] (P : AddSubmonoid Γ) (p : Γ)

/-- The ambient direct-sum decomposition induces the relative grading on `p + P`. -/
instance instDecompositionShiftedGrading : DirectSum.Decomposition (shiftedGrading ℳ P p) := by
  let 𝓝 := fun q => (ℳ q).comap (shiftedSubmodule ℳ P p).subtype
  letI : DirectSum.Decomposition 𝓝 := TauCeti.DirectSum.Decomposition.restrict ℳ 𝓝
    (shiftedSubmodule ℳ P p).subtype Subtype.val_injective (fun _ _ => Iff.rfl)
    (fun q x => ⟨⟨_, shiftedSubmodule_isHomogeneous ℳ P p q x.property⟩, rfl⟩)
  apply DirectSum.IsInternal.chooseDecomposition
  rw [funext (shiftedGrading_def ℳ P p)]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (DirectSum.Decomposition.isInternal 𝓝).submodule_iSupIndep.comp
      (add_right_injective p)
  · exact ((Equiv.addLeft p).iSup_comp (g := 𝓝)).trans
      (DirectSum.Decomposition.isInternal 𝓝).submodule_iSup_eq_top

/-- Relative homogeneous projections agree with ambient projections. -/
@[simp]
theorem coe_decompose_shiftedGrading (x : shiftedSubmodule ℳ P p) (n : Γ) :
    ((DirectSum.decompose (shiftedGrading ℳ P p) x n : shiftedSubmodule ℳ P p) : M) =
      DirectSum.decompose ℳ (x : M) (p + n) :=
  DirectSum.map_decompose_shift (shiftedGrading ℳ P p) ℳ
    (shiftedSubmodule ℳ P p).subtype.toAddMonoidHom (fun n => p + n)
    (add_right_injective p) (fun _ _ hx => (mem_shiftedGrading ℳ P p).mp hx) n x

/-- Relative homogeneous pieces outside the allowed monoid vanish. -/
@[simp]
theorem shiftedGrading_eq_bot {n : Γ} (hn : n ∉ P) : shiftedGrading ℳ P p n = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (Submodule.mem_bot R).mpr
  apply Subtype.ext
  have hz := (mem_shiftedSubmodule_iff ℳ P p).mp x.property (p + n) (by simpa using hn)
  simpa only [DirectSum.decompose_of_mem_same ℳ ((mem_shiftedGrading ℳ P p).mp hx),
    ZeroMemClass.coe_zero] using hz

namespace PositiveDegrees

variable (d : PositiveDegrees Γ)

/-- The decreasing filtration on `p + P` by the relative degree `δ(q - p)`. -/
def shiftedFiltration : ModuleFiltration R (shiftedSubmodule ℳ d.monoid p) where
  submodule k := (Mei.DirectSum.degreeTail ℳ (fun q => d.degree (q - p)) k).comap
    (shiftedSubmodule ℳ d.monoid p).subtype
  antitone := fun _ _ h => Submodule.comap_mono (Mei.DirectSum.degreeTail_antitone ℳ _ h)
  zero_eq_top := by
    apply top_unique
    intro x _
    have hs : shiftedSubmodule ℳ d.monoid p ≤
        Mei.DirectSum.degreeTail ℳ (fun q => d.degree (q - p)) 0 :=
      iSup_le fun n => Mei.DirectSum.le_degreeTail ℳ _
        (by simpa using d.degree_nonneg n.property)
    exact hs x.property

/-- Filtration membership means that all components of smaller relative degree vanish. -/
theorem mem_shiftedFiltration_iff {k : ℕ} {x : shiftedSubmodule ℳ d.monoid p} :
    x ∈ (d.shiftedFiltration ℳ p).submodule k ↔
      ∀ q, d.degree (q - p) < k → (DirectSum.decompose ℳ (x : M) q : M) = 0 :=
  Mei.DirectSum.mem_degreeTail_iff ℳ _

/-- The relative-degree filtration is separated. -/
theorem iInf_shiftedFiltration_eq_bot :
    (⨅ k, (d.shiftedFiltration ℳ p).submodule k) = ⊥ := by
  rw [shiftedFiltration, ← Submodule.comap_iInf,
    Mei.DirectSum.iInf_degreeTail_eq_bot, Submodule.comap_bot,
    LinearMap.ker_eq_bot_of_injective (shiftedSubmodule ℳ d.monoid p).injective_subtype]

/-- A homogeneous coefficient has its specified relative order, unless it is zero. -/
theorem shiftedInclusion_mem_shiftedFiltration_iff (n : d.monoid) (x : ℳ (p + n)) (k : ℕ) :
    shiftedInclusion ℳ d.monoid p n x ∈ (d.shiftedFiltration ℳ p).submodule k ↔
      x = 0 ∨ (k : ℤ) ≤ d.degree n := by
  rw [mem_shiftedFiltration_iff]
  constructor
  · intro hx
    by_cases hn : (k : ℤ) ≤ d.degree n
    · exact Or.inr hn
    · left
      apply Subtype.ext
      simpa only [coe_shiftedInclusion, add_sub_cancel_left,
        DirectSum.decompose_of_mem_same ℳ x.property, ZeroMemClass.coe_zero] using
        hx (p + n) (by simpa only [add_sub_cancel_left] using lt_of_not_ge hn)
  · rintro (rfl | hn) q hq
    · simp
    · exact DirectSum.decompose_of_mem_ne ℳ x.property (by
        intro he
        have : d.degree (q - p) = d.degree n := by rw [← he, add_sub_cancel_left]
        omega)

/-- The successor relative filtration term is the degree submodule of the relative grading.
This identifies shifted completions with the existing degree-completion construction. -/
theorem shiftedFiltration_succ (k : ℕ) :
    (d.shiftedFiltration ℳ p).submodule (k + 1) =
      d.degreeSubmodule (shiftedGrading ℳ d.monoid p) k := by
  ext x
  rw [mem_shiftedFiltration_iff, d.mem_degreeSubmodule_iff]
  constructor
  · intro hx n hn
    apply Subtype.ext
    have hn' : d.degree n < (k + 1 : ℕ) := by omega
    simpa only [coe_decompose_shiftedGrading, add_sub_cancel_left, ZeroMemClass.coe_zero] using
      hx (p + n) (by simpa only [add_sub_cancel_left] using hn')
  · intro hx q hq
    have he : p + (q - p) = q := by abel
    have hh := congrArg (fun x : shiftedSubmodule ℳ d.monoid p => (x : M))
      (hx (q - p) (by omega))
    simp only [coe_decompose_shiftedGrading, ZeroMemClass.coe_zero] at hh
    exact (congrArg (fun t => (DirectSum.decompose ℳ (x : M) t : M)) he).symm.trans hh

end PositiveDegrees
end Mei
