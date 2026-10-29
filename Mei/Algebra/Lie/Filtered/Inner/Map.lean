/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Completion
public import Mei.LinearAlgebra.ModuleFiltration.Map
public import Mei.RingTheory.FilteredAlgebra.Module

/-!
# Completing inner coefficient maps

A filtration-preserving linear coefficient map from a positively graded Lie
algebra induces maps on finite quotients and their completions. The completed
map commutes with projections and canonical images. Strict positivity places
its image in the first completion ideal, where exponentials are defined.

The coefficient map does not require a Lie action, rational scalars, or a
separated filtration. Inner-action conjugation formulas use these maps in
`Mei.Algebra.Lie.Filtered.Inner.Completed`.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

variable {N L : Type*} [AddCommMonoid N] [LieRing L] [LieAlgebra R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (j : L →ₗ[R] A)
  (hj : ∀ k, d.degreeSubmodule ℒ k ≤ ((F.ideal (k + 1)).restrictScalars R).comap j)

local notation "G" => LieIdeal.completionFiltration
  (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

include hj in
private theorem innerMap_filtered (k : ℕ) :
    (G).submodule (k + 1) ≤ ((F.toModuleFiltration R).submodule (k + 1)).comap j := by
  simpa only [LieIdeal.completionFiltration_succ, PositiveDegrees.degreeIdeal_toSubmodule,
    toModuleFiltration_submodule] using hj k

/-- The coefficient map induced on the matching Lie and algebra quotients. -/
def truncatedInnerMap (k : ℕ) : d.truncatedLie ℒ k →ₗ[R] A ⧸ F.ideal (k + 1) :=
  (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).toLinearMap.comp
    (((G).submodule (k + 1)).mapQ ((F.toModuleFiltration R).submodule (k + 1)) j
      (F.innerMap_filtered d ℒ j hj k))

/-- The truncated coefficient map sends the class of a Lie element to its coefficient class. -/
@[simp]
theorem truncatedInnerMap_mk (k : ℕ) (x : L) :
    F.truncatedInnerMap d ℒ j hj k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk (F.ideal (k + 1)) (j x) := by
  rfl

/-- Extend the inner coefficient map to the completed Lie algebra. -/
def completedInnerMap : d.completedLie ℒ →ₗ[R] F.completion :=
  (F.moduleCompletionEquiv (R := R)).toLinearMap.comp
    ((G).completionMap (F.toModuleFiltration R) j id monotone_id
      (F.innerMap_filtered d ℒ j hj))

/-- Every projection of the completed coefficient map is its finite quotient map. -/
@[simp]
theorem projection_completedInnerMap (k : ℕ) (x : d.completedLie ℒ) :
    F.projection k (F.completedInnerMap d ℒ j hj x) =
      F.truncatedInnerMap d ℒ j hj k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) := by
  simp only [completedInnerMap, LinearMap.comp_apply, projection_moduleCompletionEquiv,
    ModuleFiltration.projection_completionMap, id_eq, truncatedInnerMap,
    LinearEquiv.coe_coe, LieIdeal.completionProjection_apply]

/-- The completed extension agrees with the original coefficient map on Lie elements. -/
@[simp]
theorem completedInnerMap_toCompletion (x : L) :
    F.completedInnerMap d ℒ j hj
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      F.toCompletion (j x) := by
  apply F.completion_ext
  intro k
  simp

include hj in
/-- Strict positivity puts every original coefficient image in the first ideal. -/
theorem innerMap_mem_one (x : L) : j x ∈ F.ideal 1 := by
  have hx : x ∈ d.degreeSubmodule ℒ 0 := by simp
  exact hj 0 hx

/-- Strict positivity puts every completed coefficient image in the first completion ideal. -/
theorem completedInnerMap_mem_one (x : d.completedLie ℒ) :
    F.completedInnerMap d ℒ j hj x ∈ F.completionIdeal 1 := by
  rw [completionIdeal_succ, RingHom.mem_ker, projection_completedInnerMap]
  rw [Subsingleton.elim
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 x) 0,
    map_zero]

/-- The completed inner image with the positive-order membership needed for exponentiation. -/
def completedInnerElement (x : d.completedLie ℒ) : F.completionIdeal 1 :=
  ⟨F.completedInnerMap d ℒ j hj x, F.completedInnerMap_mem_one d ℒ j hj x⟩

/-- Forgetting positivity returns the completed coefficient map. -/
@[simp]
theorem coe_completedInnerElement (x : d.completedLie ℒ) :
    (F.completedInnerElement d ℒ j hj x : F.completion) =
      F.completedInnerMap d ℒ j hj x := (rfl)

end Mei.AlgFiltration
