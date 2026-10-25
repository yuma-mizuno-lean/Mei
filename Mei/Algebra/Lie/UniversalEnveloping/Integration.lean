/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.BCH.Completion

/-!
# Integrating completed BCH groups into enveloping units

The completed BCH group maps to all units of the completed enveloping algebra by
forgetting group-likeness in `completedBCHToGroupLike`. Finite projections uniquely
characterize this homomorphism, and its associative logarithm recovers the canonical
completed Lie coordinate.

This module reuses the group-like comparison from
`Mei.Algebra.Lie.UniversalEnveloping.BCH.Completion` and Mathlib's `Subgroup.subtype`.
The logarithm formula uses the existing completed exponential/logarithm inverse law.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "hneg" => (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))
local notation "F" => degreeFiltration ℒ d.degree hneg

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Rational scalars on the enveloping algebra are induced by the coefficient ring. -/
local instance rationalIntegratedEnvelopingAlgebra : Algebra ℚ U :=
  Algebra.compHom U (algebraMap ℚ R)

/-- Integrate the completed BCH group into the units of the completed enveloping algebra. -/
noncomputable def completedBCHToUnits : d.completedBCHGroup ℒ →* (F).completionˣ :=
  (completedGroupLikeSubgroup ℒ d.degree hneg).subtype.comp (completedBCHToGroupLike d ℒ)

/-- The completed integration map has the prescribed finite enveloping exponentials. -/
@[simp]
theorem projection_completedBCHToUnits (k : ℕ) (g : d.completedBCHGroup ℒ) :
    (F).projection k (completedBCHToUnits d ℒ g : (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1)) :=
  projection_completedBCHToGroupLike d ℒ k g

/-- The finite projection equations uniquely characterize completed integration. -/
theorem completedBCHToUnits_unique (f : d.completedBCHGroup ℒ →* (F).completionˣ)
    (hf : ∀ k g, (F).projection k (f g : (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1))) : f = completedBCHToUnits d ℒ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply (F).completion_ext
  intro k
  exact (hf k g).trans (projection_completedBCHToUnits d ℒ k g).symm

/-- The integrated value is the completed exponential of the canonical Lie image. -/
theorem coe_completedBCHToUnits (g : d.completedBCHGroup ℒ) :
    (completedBCHToUnits d ℒ g : (F).completion) =
      (F).completedExp ⟨completedLieToU d ℒ ((d.completedBCHExp ℒ).symm g),
        completedLieToU_mem_completionIdeal_one d ℒ _⟩ :=
  coe_completedBCHToGroupLike d ℒ g

/-- Completed integration takes values in the group-like subgroup. -/
theorem isCompletedGroupLike_completedBCHToUnits (g : d.completedBCHGroup ℒ) :
    IsCompletedGroupLike ℒ d.degree hneg (completedBCHToUnits d ℒ g : (F).completion) :=
  (mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mp
    (completedBCHToGroupLike d ℒ g).property

/-- Associative logarithms recover the canonical completed Lie coordinate. -/
@[simp]
theorem completedLog_completedBCHToUnits (g : d.completedBCHGroup ℒ) :
    (F).completedLog ⟨(completedBCHToUnits d ℒ g : (F).completion),
      (isCompletedGroupLike_completedBCHToUnits d ℒ g).sub_one_mem ℒ d.degree hneg
        (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)⟩ =
      completedLieToU d ℒ ((d.completedBCHExp ℒ).symm g) := by
  simp only [coe_completedBCHToUnits, Mei.AlgFiltration.completedLog_completedExp]

end Mei.UniversalEnvelopingAlgebra
