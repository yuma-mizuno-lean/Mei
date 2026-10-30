/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Correction
public import Mei.Algebra.Lie.Graded.Shifted.Component

/-!
# A degree recursion for shifted BCH actions

The component of relative degree `k + 1` in a transported shifted coefficient
is its original component plus a finite sum of contributions from input degrees
at most `k`. The summands retain entire homogeneous coefficients, with no choice
of monomial basis or restriction on spatial directions.

The formula combines `ModuleFiltration.truncatedBCHCorrection` with
`PositiveDegrees.projection_eq_sum_shiftedHomogeneousComponent`. It supplies the
algebraic step in recursions obtained by deleting the last positive-degree change
of a decorated path; see Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

/-- A transported component of relative degree `k + 1` is the original component
plus contributions from strictly lower input degrees. The sum is finite on the
actual positive monoid, which need not be saturated or finitely generated. -/
theorem shiftedHomogeneousComponent_completedBCHAction_eq_add_sum
    (g : d.completedBCHGroup ℒ) (x : d.ShiftedCoefficients ℳ p) (q : Γ) (k : ℕ)
    (hq : d.degree (q - p) = k + 1) :
    d.shiftedHomogeneousComponent ℳ p q ((F).completedBCHAction d ℒ g x) =
      d.shiftedHomogeneousComponent ℳ p q x +
        ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
            ((F).truncatedBCHAction d ℒ (k + 1) (CompletedGroup.projection (k + 1) g)
              (Submodule.Quotient.mk
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp
                    ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedHomogeneousComponent ℳ p (p + n.val) x)))) := by
  classical
  let c := d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
  let gk : d.truncatedGroup ℒ (k + 1) := CompletedGroup.projection (k + 1) g
  have he : (F).projection (k + 1) ((F).completedBCHAction d ℒ g x - x) =
      (F).truncatedBCHCorrection d ℒ k gk ((F).projection k x) :=
    (F).projection_completedBCHAction_sub d ℒ g x k
  rw [d.projection_eq_sum_shiftedHomogeneousComponent ℳ p k x] at he
  simp only [← Submodule.mkQ_apply, map_sum] at he
  have hc := congrArg c he
  simp only [Submodule.mkQ_apply, map_sub, map_sum,
    ModuleFiltration.truncatedBCHCorrection_mk] at hc
  have hzero (n : (d.finite_cutoff k).toFinset) :
      c (Submodule.Quotient.mk
        (shiftedInclusion ℳ d.monoid p
          ⟨n.val, (d.mem_cutoff.mp
            ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
          (d.shiftedHomogeneousComponent ℳ p (p + n.val) x))) = 0 := by
    rw [shiftedQuotientComponent_mk]
    apply Subtype.ext
    simp only [coe_shiftedInclusion, ZeroMemClass.coe_zero]
    apply DirectSum.decompose_of_mem_ne ℳ
      (d.shiftedHomogeneousComponent ℳ p (p + n.val) x).property
    intro hnq
    have hn := (d.mem_cutoff.mp
      ((d.finite_cutoff k).mem_toFinset.mp n.property)).2
    have heq : q - p = n.val := by rw [← hnq]; abel
    rw [heq] at hq
    omega
  simp only [hzero, sub_zero] at hc
  dsimp only [c] at hc
  rw [← d.shiftedHomogeneousComponent_eq ℳ p q (k + 1) (by omega),
    ← d.shiftedHomogeneousComponent_eq ℳ p q (k + 1) (by omega)] at hc
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

end Mei.PositiveDegrees
