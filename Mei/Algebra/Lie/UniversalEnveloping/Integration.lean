/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Coordinates
public import Mei.Algebra.Lie.UniversalEnveloping.BCH
public import Mei.Algebra.Lie.UniversalEnveloping.Exp

/-!
# Integrating completed BCH groups into enveloping units

The finite enveloping exponentials assemble into a homomorphism from the completed
BCH group to the units of the degree-completed enveloping algebra. Its values are
group-like, and their associative logarithms recover the canonical completed Lie
image. This constructs the comparison without assuming a PBW embedding or that all
completed primitives arise from Lie elements.

The construction uses `truncatedBCHToUnits`, the existing compatible-family
completion, and Mathlib's `MonoidHom.toHomUnits`. Group-likeness follows from
`isCompletedGroupLike_completedExp_iff` after checking the completed Lie image is
primitive at every finite order.
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

private noncomputable def completedBCHHom : d.completedBCHGroup ℒ →* (F).completion where
  toFun g := ⟨fun k => (truncatedBCHToUnits d ℒ k.unop (CompletedGroup.projection k.unop g) :
    U ⧸ (F).ideal (k.unop + 1)), by
      apply ((F).mem_completion_iff _).mpr
      intro k l h
      have hc := congrArg Units.val
        (factor_truncatedBCHToUnits d ℒ h (CompletedGroup.projection l g))
      have hg : (d.truncationMap ℒ h).bchGroupMap (CompletedGroup.projection l g) =
          CompletedGroup.projection k g := CompletedGroup.map_projection k l h g
      simpa only [Units.coe_map, MonoidHom.coe_ofClass, hg] using hc⟩
  map_one' := by
    apply (F).completion_ext
    intro k
    simp only [Mei.AlgFiltration.projection_apply, map_one]
    exact congrArg Units.val ((truncatedBCHToUnits d ℒ k).map_one)
  map_mul' g h := by
    apply (F).completion_ext
    intro k
    simp only [Mei.AlgFiltration.projection_apply]
    rw [(CompletedGroup.projection k).map_mul]
    exact congrArg Units.val ((truncatedBCHToUnits d ℒ k).map_mul
      (CompletedGroup.projection k g) (CompletedGroup.projection k h))

/-- Integrate the completed BCH group into the units of the completed enveloping algebra. -/
noncomputable def completedBCHToUnits : d.completedBCHGroup ℒ →* (F).completionˣ :=
  (completedBCHHom d ℒ).toHomUnits

/-- The completed integration map has the prescribed finite enveloping exponentials. -/
@[simp]
theorem projection_completedBCHToUnits (k : ℕ) (g : d.completedBCHGroup ℒ) :
    (F).projection k (completedBCHToUnits d ℒ g : (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1)) := by
  simp [completedBCHToUnits, completedBCHHom, Mei.AlgFiltration.projection_apply]

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
      (F).completedExp ⟨completedLieToU d ℒ (d.completedLogEquiv ℒ g),
        completedLieToU_mem_completionIdeal_one d ℒ _⟩ := by
  apply (F).completion_ext
  intro k
  rw [projection_completedBCHToUnits, Mei.AlgFiltration.projection_completedExp,
    projection_completedLieToU, PositiveDegrees.projection_completedLogEquiv]
  exact coe_truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g)

/-- Completed integration takes values in the group-like subgroup. -/
theorem isCompletedGroupLike_completedBCHToUnits (g : d.completedBCHGroup ℒ) :
    IsCompletedGroupLike ℒ d.degree hneg (completedBCHToUnits d ℒ g : (F).completion) := by
  rw [coe_completedBCHToUnits, isCompletedGroupLike_completedExp_iff]
  exact isCompletedPrimitive_completedLieToU d ℒ _

/-- The comparison from completed BCH labels to completed group-like units. -/
noncomputable def completedBCHToGroupLike :
    d.completedBCHGroup ℒ →* completedGroupLikeSubgroup ℒ d.degree hneg :=
  (completedBCHToUnits d ℒ).codRestrict _ (fun g =>
    (mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mpr
      (isCompletedGroupLike_completedBCHToUnits d ℒ g))

/-- Forgetting group-likeness recovers the integration homomorphism. -/
@[simp]
theorem coe_completedBCHToGroupLike (g : d.completedBCHGroup ℒ) :
    (completedBCHToGroupLike d ℒ g).val = completedBCHToUnits d ℒ g := (rfl)

/-- Associative logarithms recover the canonical completed Lie coordinate. -/
@[simp]
theorem completedLog_completedBCHToUnits (g : d.completedBCHGroup ℒ) :
    (F).completedLog ⟨(completedBCHToUnits d ℒ g : (F).completion),
      (isCompletedGroupLike_completedBCHToUnits d ℒ g).sub_one_mem ℒ d.degree hneg
        (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)⟩ =
      completedLieToU d ℒ (d.completedLogEquiv ℒ g) := by
  apply (F).completion_ext
  intro k
  rw [Mei.AlgFiltration.projection_completedLog, projection_completedLieToU,
    PositiveDegrees.projection_completedLogEquiv]
  rw [projection_completedBCHToUnits]
  exact log_truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g)

/-- A group-like unit is integrated from a completed BCH element exactly when its
associative logarithm belongs to the canonical completed Lie image. -/
theorem mem_range_completedBCHToGroupLike_iff
    (u : completedGroupLikeSubgroup ℒ d.degree hneg) :
    u ∈ (completedBCHToGroupLike d ℒ).range ↔
      ∃ x : d.completedLie ℒ, completedLieToU d ℒ x =
        (F).completedLog ⟨(u.val : (F).completion),
          ((mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mp u.property).sub_one_mem
            ℒ d.degree hneg (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)⟩ := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨d.completedLogEquiv ℒ g, (completedLog_completedBCHToUnits d ℒ g).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(d.completedLogEquiv ℒ).symm x, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_completedBCHToGroupLike, coe_completedBCHToUnits, Equiv.apply_symm_apply]
    let v : {a : (F).completion // a - 1 ∈ (F).completionIdeal 1} :=
      ⟨u.val, ((mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mp u.property).sub_one_mem
        ℒ d.degree hneg (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)⟩
    have he : (⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ :
        (F).completionIdeal 1) = ⟨(F).completedLog v, (F).completedLog_mem v⟩ := Subtype.ext hx
    exact (congrArg (F).completedExp he).trans ((F).completedExp_completedLog v)

end Mei.UniversalEnvelopingAlgebra
