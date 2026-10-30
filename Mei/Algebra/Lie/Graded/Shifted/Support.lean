/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.Algebra.PositiveDegrees.Word

/-!
# Positive degree changes under finite BCH actions

Finite exponential actions preserve the image of each translated positive
support, even when the coefficient filtration is not homogeneous. When the
quotient inherits its grading, every surviving component of a homogeneous
input differs from its input degree by an element of the positive monoid.
This applies to either sign of a BCH label.

On the existing finite shifted coefficient modules, surviving homogeneous
histories therefore have allowed degree increments and at most `k` nonzero
changes at order `k`. These are the coefficient constraints on the degree
itineraries of decorated broken lines; shifts with zero spatial direction are
retained.

The support argument uses `PositiveDegrees.lie_mem_shiftedSubmodule`,
`Module.End.exp_apply_mem_of_forall_mem`, and the inherited quotient grading.
Whole-component propagation and its positive degree convention follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]

namespace ModuleFiltration

variable (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F]

/-- Rational scalars on a coefficient quotient are induced from its scalar ring. -/
local instance quotientRatModuleSupport (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- Finite Lie exponentials preserve the image of every translated positive
support. The filtration need not respect the coefficient grading. -/
theorem truncatedExpLieAction_mem_map_shiftedSubmodule
    (k : ℕ) (x : d.truncatedLie ℒ k) (p : Γ) {a : F.quotient k}
    (ha : a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ) :
    F.truncatedExpLieAction d ℒ k x a ∈
      (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
  rw [truncatedExpLieAction_apply]
  apply Module.End.exp_apply_mem_of_forall_mem _
    ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩ _ ?_ ha
  intro b hb
  obtain ⟨y, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  obtain ⟨b, hb, rfl⟩ := hb
  rw [LieIdeal.mkQ_apply, truncatedLieAction_mk, Submodule.mkQ_apply,
    quotientLieAction_mk]
  exact Submodule.mem_map_of_mem (d.lie_mem_shiftedSubmodule ℒ ℳ p y hb)

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- BCH labels preserve and reflect every translated positive support in a
finite coefficient quotient. Inverse labels satisfy the same support condition. -/
@[simp↓]
theorem truncatedBCHAction_mem_map_shiftedSubmodule_iff
    (k : ℕ) (g : d.truncatedGroup ℒ k) (p : Γ) (a : F.quotient k) :
    F.truncatedBCHAction d ℒ k g a ∈
      (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ ↔
    a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
  have h (g : d.truncatedGroup ℒ k) {a : F.quotient k}
      (ha : a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ) :
      F.truncatedBCHAction d ℒ k g a ∈
        (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
    rw [truncatedBCHAction_apply]
    exact F.truncatedExpLieAction_mem_map_shiftedSubmodule d ℒ ℳ k _ p ha
  exact ⟨fun ha => by
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h g⁻¹ ha,
    fun ha => h g ha⟩

/-- Every surviving quotient component of a homogeneous input has an allowed
degree increment. This uses the inherited quotient decomposition, with no
finiteness or freeness hypothesis on the homogeneous pieces. -/
theorem sub_mem_monoid_of_decompose_truncatedBCHAction_ne_zero
    (k : ℕ) (g : d.truncatedGroup ℒ k)
    (𝓝 : Γ → Submodule R (F.quotient k)) [DirectSum.Decomposition 𝓝]
    (h𝓝 : ∀ n, 𝓝 n = (ℳ n).map (F.submodule (k + 1)).mkQ)
    {p q : Γ} {a : F.quotient k}
    (ha : a ∈ 𝓝 p)
    (hq : DirectSum.decompose 𝓝 (F.truncatedBCHAction d ℒ k g a) q ≠ 0) :
    q - p ∈ d.monoid := by
  have hp : ℳ p ≤ shiftedSubmodule ℳ d.monoid p := by
    simpa using le_shiftedSubmodule ℳ d.monoid p (d.monoid.zero_mem)
  have hs := (F.truncatedBCHAction_mem_map_shiftedSubmodule_iff d ℒ ℳ k g p a).mpr
    (Submodule.map_mono hp (by simpa only [h𝓝] using ha))
  have he : (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ =
      shiftedSubmodule 𝓝 d.monoid p := by
    simp only [shiftedSubmodule_def, Submodule.map_iSup, h𝓝]
  rw [he] at hs
  by_contra h
  exact hq (Subtype.val_injective
    ((mem_shiftedSubmodule_iff _ d.monoid p).mp hs q h))

end ModuleFiltration

end Mei

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DirectSum.Decomposition ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

/-- A surviving component of the actual finite shifted BCH action has an
allowed relative degree increment, for any label, including an inverse label. -/
theorem sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero
    (k : ℕ) (g : d.truncatedGroup ℒ k) {r s : Γ} {a : (F).quotient k}
    (ha : a ∈ (d.shiftedQuotientGrading ℳ p k).piece r)
    (hs : DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
      ((F).truncatedBCHAction d ℒ k g a) s ≠ 0) :
    s - r ∈ d.monoid := by
  have := d.shiftedGrading_gradedBracket ℒ ℳ p
  exact (F).sub_mem_monoid_of_decompose_truncatedBCHAction_ne_zero
    (M := d.shiftedLieSubmodule ℒ ℳ p)
    d ℒ (shiftedGrading ℳ d.monoid p) k g ((d.shiftedQuotientGrading ℳ p k).piece)
      (d.shiftedQuotientGrading_piece ℳ p k) ha hs

/-- Every step of a surviving whole-component history of actual finite BCH
actions changes degree by an element of the positive monoid. Identity encounters
are retained; no spatial projection is used. -/
theorem homogeneousHistory_shiftedBCHAction_sub_mem_monoid
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0) (j : Fin n) :
    r j - Fin.snoc (α := fun _ => Γ) r r₀ j.succ ∈ d.monoid := by
  let T := fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap
  apply d.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero ℒ ℳ p k (g j)
    (homogeneousHistoryStage_mem_snoc _ T r r₀ a j.succ)
  intro hz
  have hs := homogeneousHistoryStage_ne_zero (d.shiftedQuotientGrading ℳ p k).piece
    (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r hne j.castSucc
  apply hs
  rw [homogeneousHistoryStage_castSucc_apply]
  exact congrArg Subtype.val hz

/-- Reading a surviving history backwards, any earlier degree differs from
any later degree by an allowed increment. The comparison includes the incoming
segment and supplies decreasing-degree itineraries without an extra hypothesis. -/
theorem homogeneousHistory_shiftedBCHAction_sub_mem_monoid_of_le
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Fin.snoc (α := fun _ => Γ) r r₀ i - Fin.snoc (α := fun _ => Γ) r r₀ j ∈
      d.monoid := by
  induction j using Fin.inductionOn with
  | zero =>
    have hi : i = 0 := le_antisymm hij (Fin.zero_le i)
    subst i
    simp
  | succ j ih =>
    by_cases he : i = j.succ
    · subst i
      simp
    · have hle : i ≤ j.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hij he)
      have hstep :=
        d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid ℒ ℳ p k g r r₀ a hne j
      simpa only [Fin.snoc_castSucc, sub_add_sub_cancel] using
        d.monoid.add_mem (ih hle) hstep

/-- A surviving history of finite shifted BCH actions has at most `k` nonzero
degree changes at order `k`. Unchanged-degree encounters are not counted, while
nonzero shifts with unchanged spatial velocity are counted. -/
theorem length_filter_bne_zero_homogeneousHistory_shiftedBCHAction_le
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0) :
    ((List.ofFn fun j => r j - Fin.snoc (α := fun _ => Γ) r r₀ j.succ).filter
      (· != 0)).length ≤ k := by
  let T := fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap
  let b := Fin.snoc (α := fun _ => Γ) r r₀
  have hcut (j : Fin (n + 1)) : b j ∈ d.cutoff k :=
    d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p
      (homogeneousHistoryStage_mem_snoc _ T r r₀ a j)
      (homogeneousHistoryStage_ne_zero _ T r hne j)
  apply d.length_filter_bne_zero_le
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid ℒ ℳ p k g r r₀ a hne j
  · have hsum : (List.ofFn fun j => r j - b j.succ).sum = b 0 - r₀ := by
      rw [Fin.sum_ofFn, Finset.sum_sub_distrib]
      have he := (Fin.sum_univ_succ b).symm.trans (Fin.sum_univ_castSucc b)
      simp only [b, Fin.snoc_castSucc, Fin.snoc_last] at he
      -- The difference of the two endpoint decompositions is the telescoping sum.
      calc
        _ = ((∑ j, r j) + r₀) - (b 0 + ∑ j : Fin n, b j.succ) + (b 0 - r₀) := by abel
        _ = _ := by rw [← he]; abel
    rw [hsum, map_sub]
    have hlast := d.degree_nonneg (d.mem_cutoff.mp (hcut (Fin.last n))).1
    have hfirst := (d.mem_cutoff.mp (hcut 0)).2
    simp only [b, Fin.snoc_last] at hlast
    omega

end Mei.PositiveDegrees
