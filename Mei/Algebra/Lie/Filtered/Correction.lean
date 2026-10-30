/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Lower-order dependence of filtered BCH corrections

A filtration-raising Lie action induces zero on each associated graded piece, so the
integrated BCH action induces the identity. The difference from the identity at order
`k + 1` thus factors through the coefficient quotient of order `k`.
`truncatedBCHCorrection` is this linear map. Its evaluation formula expresses the
new coefficient using only lower-order input; its product law also applies to
noncommuting successive wall crossings.

On the completion, every BCH correction raises coefficient order by at least one.
Thus two inputs agreeing below order `b` have corrections agreeing through order
`b`. These statements provide the algebraic triangularity used in degree
recursions for transported coefficients.
-/

public noncomputable section

namespace Mei.ModuleFiltration

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

private local instance correctionQuotientRatModule (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- The finite BCH action fixes the highest retained filtration term pointwise. -/
theorem truncatedBCHAction_mk_eq_self_of_mem (k : ℕ) (g : d.truncatedGroup ℒ k)
    {m : M} (hm : m ∈ F.submodule k) :
    F.truncatedBCHAction d ℒ k g (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
  rw [truncatedBCHAction_apply, truncatedExpLieAction_apply]
  apply Module.End.exp_apply_eq_self _ ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k _⟩
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ k).surjective_mkQ (BCHGroup.log g)
  rw [← hx, LieIdeal.mkQ_apply, truncatedLieAction_mk, quotientLieAction_mk,
    Submodule.Quotient.mk_eq_zero]
  exact F.lie_mem_succ d ℒ x hm

/-- The order-`k + 1` correction to a BCH action, as a linear function of
coefficients retained only through order `k`. -/
def truncatedBCHCorrection (k : ℕ) (g : d.truncatedGroup ℒ (k + 1)) :
    F.quotient k →ₗ[R] F.quotient (k + 1) :=
  (F.submodule (k + 1)).liftQ
    (((F.truncatedBCHAction d ℒ (k + 1) g).toLinearMap - LinearMap.id).comp
      (F.submodule (k + 1 + 1)).mkQ) (by
        intro m hm
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearEquiv.coe_coe, LinearMap.id_apply, Submodule.mkQ_apply]
        exact sub_eq_zero.mpr (F.truncatedBCHAction_mk_eq_self_of_mem d ℒ (k + 1) g hm))

/-- On any representative the correction is the action minus that representative
in the next finer quotient. -/
@[simp]
theorem truncatedBCHCorrection_mk (k : ℕ) (g : d.truncatedGroup ℒ (k + 1)) (m : M) :
    F.truncatedBCHCorrection d ℒ k g (Submodule.Quotient.mk m) =
      F.truncatedBCHAction d ℒ (k + 1) g (Submodule.Quotient.mk m) -
        Submodule.Quotient.mk m := by
  simp only [truncatedBCHCorrection, Submodule.liftQ_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Submodule.mkQ_apply]

/-- Every finite BCH action is the input plus a correction determined one order
earlier. -/
theorem truncatedBCHAction_eq_add_correction (k : ℕ)
    (g : d.truncatedGroup ℒ (k + 1)) (a : F.quotient (k + 1)) :
    F.truncatedBCHAction d ℒ (k + 1) g a =
      a + F.truncatedBCHCorrection d ℒ k g (F.transition (Nat.le_succ k) a) := by
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1 + 1)).mkQ_surjective a
  simp

/-- The identity label has zero correction. -/
@[simp]
theorem truncatedBCHCorrection_one (k : ℕ) :
    F.truncatedBCHCorrection d ℒ k 1 = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  simp

/-- Corrections of successive labels satisfy the cocycle identity. No
commutation between the two labels is required. -/
theorem truncatedBCHCorrection_mul (k : ℕ) (g h : d.truncatedGroup ℒ (k + 1))
    (a : F.quotient k) :
    F.truncatedBCHCorrection d ℒ k (g * h) a =
      F.truncatedBCHAction d ℒ (k + 1) g (F.truncatedBCHCorrection d ℒ k h a) +
        F.truncatedBCHCorrection d ℒ k g a := by
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  simp only [Submodule.mkQ_apply, truncatedBCHCorrection_mk, map_mul,
    LinearEquiv.mul_apply, map_sub]
  abel

/-- Lowering both cutoffs commutes with correction maps. -/
theorem transition_truncatedBCHCorrection {k l : ℕ} (hkl : k ≤ l)
    (g : d.truncatedGroup ℒ (l + 1)) (a : F.quotient l) :
    F.transition (Nat.add_le_add_right hkl 1) (F.truncatedBCHCorrection d ℒ l g a) =
      F.truncatedBCHCorrection d ℒ k
        ((d.truncationMap ℒ (Nat.add_le_add_right hkl 1)).bchGroupMap g)
        (F.transition hkl a) := by
  obtain ⟨m, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective a
  simp only [Submodule.mkQ_apply, truncatedBCHCorrection_mk, map_sub,
    transition_truncatedBCHAction, transition_mk]

/-- At order `k + 1`, corrections of inputs with the same order-`k` truncation
are equal. This isolates the lower-degree data needed in a recursive computation. -/
theorem truncatedBCHAction_sub_eq_of_transition_eq (k : ℕ)
    (g : d.truncatedGroup ℒ (k + 1)) {a b : F.quotient (k + 1)}
    (hab : F.transition (Nat.le_succ k) a = F.transition (Nat.le_succ k) b) :
    F.truncatedBCHAction d ℒ (k + 1) g a - a =
      F.truncatedBCHAction d ℒ (k + 1) g b - b := by
  rw [F.truncatedBCHAction_eq_add_correction d ℒ k g a,
    F.truncatedBCHAction_eq_add_correction d ℒ k g b, hab]
  abel

/-- Every completed BCH action induces the identity on the associated graded:
its difference from the identity raises coefficient order by one. -/
theorem completedBCHAction_sub_mem_completedFiltration (g : d.completedBCHGroup ℒ)
    {b : ℕ} {a : F.completion} (ha : a ∈ F.completedFiltration.submodule b) :
    F.completedBCHAction d ℒ g a - a ∈ F.completedFiltration.submodule (b + 1) := by
  rw [completedFiltration_succ, LinearMap.mem_ker, map_sub,
    projection_completedBCHAction, sub_eq_zero]
  obtain ⟨m, hm, he⟩ := F.exists_projection_eq_of_mem_completedFiltration ha (k := b)
  rw [← he]
  exact F.truncatedBCHAction_mk_eq_self_of_mem d ℒ b _ hm

/-- The finite correction computes each completed correction using one less
coefficient order than the output order. -/
theorem projection_completedBCHAction_sub (g : d.completedBCHGroup ℒ)
    (a : F.completion) (k : ℕ) :
    F.projection (k + 1) (F.completedBCHAction d ℒ g a - a) =
      F.truncatedBCHCorrection d ℒ k (CompletedGroup.projection (k + 1) g)
        (F.projection k a) := by
  simp only [map_sub, projection_completedBCHAction,
    F.truncatedBCHAction_eq_add_correction d ℒ k (CompletedGroup.projection (k + 1) g),
    transition_projection, add_sub_cancel_left]

end Mei.ModuleFiltration
