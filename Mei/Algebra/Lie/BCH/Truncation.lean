/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion

/-!
# Completing a finite Lie truncation

The completed BCH group of the grading on `L / F^{k+1}L` is canonically the
order-`k` BCH group of `L`. Under this equivalence, the completed map induced by
the quotient homomorphism is exactly projection to order `k`. Consequently, applying
a coefficient map to a wall label with this quotient really discards precisely its
terms above order `k`, even though the mapped label is formally a completed element.

The equivalence uses `PositiveDegrees.bchCompletionEquiv`: the quotient grading
has no pieces above its retained cutoff. The original Lie algebra need not be
nilpotent or bounded.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Completing the grading on a finite Lie truncation recovers its BCH group. -/
def truncatedBCHCompletionEquiv (k : ℕ) :
    d.completedBCHGroup (d.truncatedGrading ℒ k) ≃* d.truncatedGroup ℒ k :=
  (d.bchCompletionEquiv (d.truncatedGrading ℒ k)
    (d.degreeIdeal_truncatedGrading_eq_bot ℒ le_rfl)).symm

/-- The inverse comparison is the canonical map into the completion. -/
@[simp]
theorem truncatedBCHCompletionEquiv_symm_apply (k : ℕ) (g : d.truncatedGroup ℒ k) :
    (d.truncatedBCHCompletionEquiv ℒ k).symm g =
      d.bchToCompletion (d.truncatedGrading ℒ k) g := by
  rw [truncatedBCHCompletionEquiv, MulEquiv.symm_symm, bchCompletionEquiv_apply]

/-- A completed exponential in the truncated algebra has its original finite coordinate. -/
@[simp]
theorem truncatedBCHCompletionEquiv_expToCompletion (k : ℕ) (x : d.truncatedLie ℒ k) :
    d.truncatedBCHCompletionEquiv ℒ k
      (d.expToCompletion (d.truncatedGrading ℒ k) x) = BCHGroup.exp x := by
  rw [truncatedBCHCompletionEquiv, bchCompletionEquiv_symm_expToCompletion]

/-- Quotienting the Lie algebra and then completing induces exactly the finite
projection on the original completed BCH group. -/
@[simp]
theorem truncatedBCHCompletionEquiv_completedMap_truncation (k : ℕ)
    (g : d.completedBCHGroup ℒ) :
    d.truncatedBCHCompletionEquiv ℒ k
      ((GradedLieHom.truncation d ℒ k).completedMap g) =
        CompletedGroup.projection k g := by
  apply (d.truncatedBCHCompletionEquiv ℒ k).symm.injective
  rw [MulEquiv.symm_apply_apply]
  refine Eq.trans ?_ (d.truncatedBCHCompletionEquiv_symm_apply ℒ k
    (CompletedGroup.projection k g)).symm
  apply CompletedGroup.ext
  intro l
  -- Compare at a common upper cutoff using `GradedLieHom.truncatedMap_mk`
  -- and `CompletedGroup.map_projection`.
  let f := GradedLieHom.truncation d ℒ k
  have hmap : f.truncatedMap l (a := max k l) (by simp) =
      (d.degreeIdeal (d.truncatedGrading ℒ k) l).mkQ.comp
        (d.truncationMap ℒ (le_max_left k l)) := by
    apply (d.degreeIdeal ℒ (max k l)).lieHom_qext
    intro x
    simp [f, LieIdeal.mkQ_apply]
  let gm : d.truncatedGroup ℒ (max k l) := CompletedGroup.projection (max k l) g
  let gk : d.truncatedGroup ℒ k := CompletedGroup.projection k g
  have hp : (f.truncatedMap l (a := max k l) (by simp)).bchGroupMap gm =
      (d.degreeIdeal (d.truncatedGrading ℒ k) l).mkQ.bchGroupMap gk := by
    rw [hmap, LieHom.bchGroupMap_comp, MonoidHom.comp_apply]
    exact congrArg (d.degreeIdeal (d.truncatedGrading ℒ k) l).mkQ.bchGroupMap
      (CompletedGroup.map_projection k (max k l) (le_max_left k l) g)
  exact (f.projection_completedMap_of_le l (a := max k l) (by simp) g).trans
    (hp.trans (d.projection_bchToCompletion (d.truncatedGrading ℒ k) l gk).symm)

end Mei.PositiveDegrees
