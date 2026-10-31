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

/-- The highest retained component of a BCH correction is the finite sum of
the action on all strictly lower homogeneous input components. The
coefficient is supplied only at the preceding cutoff. -/
theorem shiftedQuotientComponent_truncatedBCHCorrection_eq_sum
    (k : ℕ) (g : d.truncatedGroup ℒ (k + 1)) (x : (F).quotient k)
    (q : Γ) (hq : d.degree (q - p) = k + 1) :
    d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
        ((F).truncatedBCHCorrection d ℒ k g x) =
        ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
            ((F).truncatedBCHAction d ℒ (k + 1) g
              (Submodule.Quotient.mk
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp
                    ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedQuotientComponent ℳ p (p + n.val) k
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp
                        n.property)).2)
                    x)))) := by
  classical
  conv_lhs => rw [d.quotient_eq_sum_shiftedQuotientComponent ℳ p k x]
  simp only [ModuleFiltration.truncatedBCHCorrection_mk]
  simp only [← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply, map_sub]
  have hne (n : (d.finite_cutoff k).toFinset) : p + n.val ≠ q := by
    intro hnq
    have hn := (d.mem_cutoff.mp
      ((d.finite_cutoff k).mem_toFinset.mp n.property)).2
    have heq : q - p = n.val := by rw [← hnq]; abel
    rw [heq] at hq
    omega
  have hzero (n : (d.finite_cutoff k).toFinset) (y : ℳ (p + n.val)) :
      d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
        (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
        ⟨n.val, (d.mem_cutoff.mp
          ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩ y)) = 0 :=
    d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne ℳ p q (k + 1)
      (by omega) ⟨n.val, (d.mem_cutoff.mp
        ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩ (hne n) y
  simp only [map_sum, hzero, Finset.sum_const_zero, sub_zero]

/-- At finite order, a transported component of relative degree `k + 1` is its
original value plus contributions from input components retained at order `k`.
No lift of the group element or coefficient to a completion is needed. -/
theorem shiftedQuotientComponent_truncatedBCHAction_eq_add_sum
    (k : ℕ) (g : d.truncatedGroup ℒ (k + 1)) (x : (F).quotient (k + 1))
    (q : Γ) (hq : d.degree (q - p) = k + 1) :
    d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
        ((F).truncatedBCHAction d ℒ (k + 1) g x) =
      d.shiftedQuotientComponent ℳ p q (k + 1) (by omega) x +
        ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedQuotientComponent ℳ p q (k + 1) (by omega)
            ((F).truncatedBCHAction d ℒ (k + 1) g
              (Submodule.Quotient.mk
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp
                    ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedQuotientComponent ℳ p (p + n.val) k
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp
                        n.property)).2)
                    ((d.shiftedFiltration ℳ p).transition (Nat.le_succ k) x))))) := by
  rw [(F).truncatedBCHAction_eq_add_correction d ℒ k g x, map_add,
    d.shiftedQuotientComponent_truncatedBCHCorrection_eq_sum ℒ ℳ p k g _ q hq]

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
  rw [d.shiftedHomogeneousComponent_eq ℳ p q (k + 1) (by omega),
    (F).projection_completedBCHAction,
    d.shiftedQuotientComponent_truncatedBCHAction_eq_add_sum ℒ ℳ p k
      (CompletedGroup.projection (k + 1) g) _ q hq,
    ← d.shiftedHomogeneousComponent_eq ℳ p q (k + 1) (by omega)]
  simp only [ModuleFiltration.transition_projection,
    ← d.shiftedHomogeneousComponent_eq]

end Mei.PositiveDegrees
