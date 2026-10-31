/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.ModuleFiltration.Map

/-!
# Maps of shifted coefficient modules

A homogeneous linear map along a positive degree map restricts to each shifted
module and extends to its completion. The degree map's cutoff modulus controls
which source quotient computes a target quotient, allowing changes of the degree
function and maps that merge degrees. Neither the degree map nor the linear map
needs to be injective.

The induced finite quotient maps preserve the inherited homogeneous pieces.

The completion is the existing `ModuleFiltration.completionMap`; its defining
projection and coefficient-image laws determine the shifted extension. This is
the shifted coefficient setting of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegreeMap

section Monoid

variable {Γ Γ' R M M' : Type*} [AddCommMonoid Γ] [AddCommMonoid Γ']
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M') (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- Homogeneous maps preserve shifted support along their degree map. -/
theorem map_mem_shiftedSubmodule {x : M} (hx : x ∈ shiftedSubmodule ℳ d.monoid p) :
    f x ∈ shiftedSubmodule 𝓝 e.monoid (T p) := by
  rw [shiftedSubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => f x ∈ shiftedSubmodule 𝓝 e.monoid (T p)) hx ?_ ?_ ?_
  · intro n x hx
    apply le_shiftedSubmodule 𝓝 e.monoid (T p) (T.map_mem n.property)
    simpa only [map_add, Submodule.mem_comap] using hf (p + n) hx
  · simp
  · intro x y hx hy
    simpa only [_root_.map_add] using Submodule.add_mem _ hx hy

/-- Restrict a homogeneous coefficient map to a shifted module. -/
def shiftedMap : shiftedSubmodule ℳ d.monoid p →ₗ[R]
    shiftedSubmodule 𝓝 e.monoid (T p) :=
  (f.comp (shiftedSubmodule ℳ d.monoid p).subtype).codRestrict _
    (fun x => T.map_mem_shiftedSubmodule ℳ 𝓝 p f hf x.property)

/-- The restricted coefficient map has the same ambient values. -/
@[simp]
theorem coe_shiftedMap (x : shiftedSubmodule ℳ d.monoid p) :
    (T.shiftedMap ℳ 𝓝 p f hf x : M') = f x := (rfl)

/-- Relative degree `n` is carried to relative degree `T n`. -/
theorem shiftedMap_mem_shiftedGrading {n : Γ} {x : shiftedSubmodule ℳ d.monoid p}
    (hx : x ∈ shiftedGrading ℳ d.monoid p n) :
    T.shiftedMap ℳ 𝓝 p f hf x ∈ shiftedGrading 𝓝 e.monoid (T p) (T n) := by
  rw [mem_shiftedGrading, coe_shiftedMap]
  simpa only [map_add, Submodule.mem_comap] using
    hf (p + n) ((mem_shiftedGrading ℳ d.monoid p).mp hx)

end Monoid

section Filtration

variable {Γ Γ' R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [DecidableEq Γ]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- The degree map's modulus bounds the source filtration needed at each target order. -/
theorem shiftedMap_mem_shiftedFiltration (k : ℕ)
    {x : shiftedSubmodule ℳ d.monoid p}
    (hx : x ∈ (d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)) :
    T.shiftedMap ℳ 𝓝 p f hf x ∈ (e.shiftedFiltration 𝓝 (T p)).submodule (k + 1) := by
  rw [d.shiftedFiltration_succ ℳ p] at hx
  rw [d.degreeSubmodule_def] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => T.shiftedMap ℳ 𝓝 p f hf x ∈
      (e.shiftedFiltration 𝓝 (T p)).submodule (k + 1)) hx ?_ ?_ ?_
  · intro n x hx
    by_cases hn : n.val ∈ d.monoid
    · rw [e.shiftedFiltration_submodule 𝓝 (T p), Submodule.mem_comap,
        Submodule.subtype_apply, coe_shiftedMap]
      apply Mei.DirectSum.le_degreeTail 𝓝 _ (i := T (p + n))
      · have hd := T.degree_gt k hn n.property
        simp only [map_add, add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
        omega
      · exact hf (p + n) ((mem_shiftedGrading ℳ d.monoid p).mp hx)
    · rw [shiftedGrading_eq_bot ℳ d.monoid p hn, Submodule.mem_bot] at hx
      simp [hx]
  · simp
  · intro x y hx hy
    simpa only [_root_.map_add] using Submodule.add_mem _ hx hy

end Filtration

section Group

variable {Γ Γ' R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [DecidableEq Γ]
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

include hf

/-- The finite quotient map at the source cutoff specified by the degree modulus. -/
def shiftedQuotientMap (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient (T.modulus k) →ₗ[R]
      (e.shiftedFiltration 𝓝 (T p)).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)).mapQ
    ((e.shiftedFiltration 𝓝 (T p)).submodule (k + 1))
    (T.shiftedMap ℳ 𝓝 p f hf) (fun _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx)

/-- The finite shifted map is the induced map between the selected filtration quotients. -/
theorem shiftedQuotientMap_def (k : ℕ) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k =
      ((d.shiftedFiltration ℳ p).submodule (T.modulus k + 1)).mapQ
        ((e.shiftedFiltration 𝓝 (T p)).submodule (k + 1))
        (T.shiftedMap ℳ 𝓝 p f hf)
        (fun _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx) := (rfl)

/-- The finite shifted map sends a coefficient class to the class of its image. -/
@[simp]
theorem shiftedQuotientMap_mk (k : ℕ) (x : shiftedSubmodule ℳ d.monoid p) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (T.shiftedMap ℳ 𝓝 p f hf x) := (rfl)

/-- The induced map on the existing shifted coefficient completions. -/
def shiftedCompletionMap : d.ShiftedCoefficients ℳ p →ₗ[R] e.ShiftedCoefficients 𝓝 (T p) :=
  (d.shiftedFiltration ℳ p).completionMap (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
    (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx)

/-- The shifted extension is the existing completion map for the restricted coefficient map. -/
theorem shiftedCompletionMap_def :
    T.shiftedCompletionMap ℳ 𝓝 p f hf =
      (d.shiftedFiltration ℳ p).completionMap (e.shiftedFiltration 𝓝 (T p))
        (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus
        (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx) := (rfl)

/-- A target finite projection is computed at the source cutoff given by the modulus. -/
@[simp]
theorem projection_shiftedCompletionMap (k : ℕ) (x : d.ShiftedCoefficients ℳ p) :
    (e.shiftedFiltration 𝓝 (T p)).projection k (T.shiftedCompletionMap ℳ 𝓝 p f hf x) =
      T.shiftedQuotientMap ℳ 𝓝 p f hf k ((d.shiftedFiltration ℳ p).projection (T.modulus k) x) :=
  (d.shiftedFiltration ℳ p).projection_completionMap (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus _ k x

/-- The completed shifted map extends the original homogeneous coefficient map. -/
@[simp]
theorem shiftedCompletionMap_of (x : shiftedSubmodule ℳ d.monoid p) :
    T.shiftedCompletionMap ℳ 𝓝 p f hf ((d.shiftedFiltration ℳ p).of x) =
      (e.shiftedFiltration 𝓝 (T p)).of (T.shiftedMap ℳ 𝓝 p f hf x) :=
  (d.shiftedFiltration ℳ p).completionMap_of (e.shiftedFiltration 𝓝 (T p))
    (T.shiftedMap ℳ 𝓝 p f hf) T.modulus T.monotone_modulus _ x

end Group

section QuotientGrading

variable {Γ Γ' : Type} {R M M' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] (p : Γ)
  (f : M →ₗ[R] M') (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)

/-- The induced finite coefficient map preserves relative homogeneous pieces
along the degree map, at the source order specified by its cutoff modulus. -/
theorem shiftedQuotientMap_mem_shiftedQuotientGrading
    (k : ℕ) {n : Γ}
    {x : (d.shiftedFiltration ℳ p).quotient (T.modulus k)}
    (hx : x ∈ (d.shiftedQuotientGrading ℳ p (T.modulus k)).piece n) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k x ∈
      (e.shiftedQuotientGrading 𝓝 (T p) k).piece (T n) := by
  obtain ⟨a, ha, rfl⟩ := (d.mem_shiftedQuotientGrading_iff ℳ p).mp hx
  exact (e.mem_shiftedQuotientGrading_iff 𝓝 (T p)).mpr
    ⟨T.shiftedMap ℳ 𝓝 p f hf a,
      T.shiftedMap_mem_shiftedGrading ℳ 𝓝 p f hf ha, (T.shiftedQuotientMap_mk ..).symm⟩

end QuotientGrading

end Mei.PositiveDegreeMap
