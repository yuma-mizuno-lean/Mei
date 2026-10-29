/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Exp
public import Mei.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.Algebra.Lie.InnerAutomorphism

/-!
# Exponentiating inner actions on filtered algebras

If a Lie element acts on a filtered associative algebra by commutator with an element
of the first filtration ideal, its exponential action on the completion is conjugation
by the completed exponential of that element. This compares the exponential of the
coefficient representation with the exponential inside the coefficient algebra, without
requiring the original element or derivation to be nilpotent.

The finite comparison uses `TauCeti.expAd_apply_eq_exp_mul_exp_neg` on each quotient.
The completed comparison follows by projections, using the existing `AlgFiltration.expAction`
and `AlgFiltration.completedExp` constructions.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.AlgFiltration

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]
  [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)]

/-- An inner coefficient action descends to the adjoint action on every quotient. -/
theorem quotientLieAction_eq_ad (k : ℕ) {x : L} {y : A}
    (hxy : ∀ a, ⁅x, a⁆ = y * a - a * y) :
    F.quotientLieAction d ℒ k x =
      LieAlgebra.ad R (A ⧸ F.ideal (k + 1)) (Ideal.Quotient.mk _ y) := by
  ext q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [hxy, Ring.lie_def]

variable [IsDerivationAction L A] [Algebra ℚ A]

/-- At finite order, exponentiating an inner coefficient action is conjugation by the
finite exponential of its implementing element. -/
theorem quotientExpLieAction_apply_eq_exp_mul_exp_neg (k : ℕ) {x : L} {y : A}
    (hxy : ∀ a, ⁅x, a⁆ = y * a - a * y) (hy : y ∈ F.ideal 1)
    (a : A ⧸ F.ideal (k + 1)) :
    F.quotientExpLieAction d ℒ k x a =
      IsNilpotent.exp (Ideal.Quotient.mk (F.ideal (k + 1)) y) * a *
        IsNilpotent.exp (-Ideal.Quotient.mk (F.ideal (k + 1)) y) := by
  have hy' := (F.toCompletion_mem_completionIdeal_iff 1 y).mpr hy
  have hn : IsNilpotent (Ideal.Quotient.mk (F.ideal (k + 1)) y) := by
    simpa only [projection_toCompletion] using F.isNilpotent_projection hy' k
  rw [quotientExpLieAction_apply, F.quotientLieAction_eq_ad d ℒ k hxy]
  exact (TauCeti.expAd_apply _ (LieAlgebra.ad_nilpotent_of_nilpotent (R := R) hn) a).symm.trans
    (TauCeti.expAd_apply_eq_exp_mul_exp_neg (K := R) hn)

/-- Exponentiating an inner filtration-raising action on the completion is conjugation
by the completed exponential. The inverse factor is the exponential of the negative. -/
theorem expAction_apply_eq_completedExp_mul (x : L) (y : A)
    (hxy : ∀ a, ⁅x, a⁆ = y * a - a * y) (hy : y ∈ F.ideal 1)
    (a : F.completion) :
    F.expAction d ℒ x a =
      F.completedExp ⟨F.toCompletion y, (F.toCompletion_mem_completionIdeal_iff 1 y).mpr hy⟩ *
        a * F.completedExp (-⟨F.toCompletion y,
          (F.toCompletion_mem_completionIdeal_iff 1 y).mpr hy⟩) := by
  apply F.completion_ext
  intro k
  simp only [projection_expAction, map_mul, projection_completedExp, Submodule.coe_neg, map_neg,
    projection_toCompletion]
  exact F.quotientExpLieAction_apply_eq_exp_mul_exp_neg d ℒ k hxy hy _

end Mei.AlgFiltration
