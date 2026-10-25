/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.BCH.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.Exp
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Completion
public import Mei.Algebra.Lie.BCH.Coordinates

/-!
# Completed BCH groups in enveloping units

The completed BCH group of a positively graded Lie algebra maps canonically to
the group-like units of its degree-completed enveloping algebra. Projection is
the finite enveloping exponential, and logarithm recovers the canonical image of
the completed Lie coordinate. The image consists exactly of the group-like units
whose logarithm comes from the completed Lie algebra. Finite Dynkin
reconstruction and homogeneous assembly show that every group-like unit occurs.

The construction combines `Mei.PositiveDegrees.completedBCHExp`, the canonical
`Mei.UniversalEnvelopingAlgebra.completedLieToU`, and
`Mei.UniversalEnvelopingAlgebra.completedPrimitiveExpUnitsEquiv`.
Multiplicativity follows from `truncatedBCHToUnits` at every finite cutoff.
Neither a PBW theorem nor a free underlying module is assumed; injectivity
is not asserted here.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "hneg" => (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))
local notation "hpos" => (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)
local notation "F" => degreeFiltration ℒ d.degree hneg
local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
local notation "G" => completedGroupLikeSubgroup ℒ d.degree hneg

/-- Rational scalars on the enveloping algebra are induced from the coefficient ring. -/
local instance rationalCompletedBCHEnvelopingAlgebra : Algebra ℚ U :=
  Algebra.compHom U (algebraMap ℚ R)

private noncomputable def groupLikeExp (x : d.completedLie ℒ) : G :=
  completedPrimitiveExpUnitsEquiv ℒ d.degree hneg hpos
    ⟨⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩,
      isCompletedPrimitive_completedLieToU d ℒ x⟩

private theorem coe_groupLikeExp (x : d.completedLie ℒ) :
    ((groupLikeExp d ℒ x).val : (F).completion) =
      (F).completedExp ⟨completedLieToU d ℒ x,
        completedLieToU_mem_completionIdeal_one d ℒ x⟩ := by
  simp only [groupLikeExp, coe_completedPrimitiveExpUnitsEquiv]

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

private theorem projection_groupLikeExp (k : ℕ) (x : d.completedLie ℒ) :
    (F).projection k ((groupLikeExp d ℒ x).val : (F).completion) =
      (truncatedBCHToUnits d ℒ k (BCHGroup.exp (π k x)) : U ⧸ (F).ideal (k + 1)) := by
  simp only [coe_groupLikeExp, Mei.AlgFiltration.projection_completedExp,
    projection_completedLieToU, coe_truncatedBCHToUnits, BCHGroup.log_exp]

private theorem projection_groupLikeExp_symm (k : ℕ) (g : d.completedBCHGroup ℒ) :
    (F).projection k ((groupLikeExp d ℒ ((d.completedBCHExp ℒ).symm g)).val :
      (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1)) := by
  rw [projection_groupLikeExp, PositiveDegrees.completionProjection_completedBCHExp_symm]
  exact congrArg (fun a => (truncatedBCHToUnits d ℒ k a : U ⧸ (F).ideal (k + 1)))
    (BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g))

/-- The canonical homomorphism from completed BCH labels to completed group-like units. -/
noncomputable def completedBCHToGroupLike : d.completedBCHGroup ℒ →* G where
  toFun g := groupLikeExp d ℒ ((d.completedBCHExp ℒ).symm g)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply (F).completion_ext
    intro k
    simp only [projection_groupLikeExp_symm, map_one, Units.val_one, Subgroup.coe_one]
    exact congrArg Units.val ((truncatedBCHToUnits d ℒ k).map_one)
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    apply (F).completion_ext
    intro k
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul, projection_groupLikeExp_symm]
    exact congrArg Units.val ((truncatedBCHToUnits d ℒ k).map_mul
      (CompletedGroup.projection k g) (CompletedGroup.projection k h))

/-- The value of the completed group map is exponential of the canonical Lie image. -/
@[simp]
theorem coe_completedBCHToGroupLike (g : d.completedBCHGroup ℒ) :
    ((completedBCHToGroupLike d ℒ g).val : (F).completion) =
      (F).completedExp ⟨completedLieToU d ℒ ((d.completedBCHExp ℒ).symm g),
        completedLieToU_mem_completionIdeal_one d ℒ _⟩ :=
  coe_groupLikeExp d ℒ _

/-- Each projection of the completed group map is the existing finite unit map. -/
theorem projection_completedBCHToGroupLike (k : ℕ) (g : d.completedBCHGroup ℒ) :
    (F).projection k ((completedBCHToGroupLike d ℒ g).val : (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1)) :=
  projection_groupLikeExp_symm d ℒ k g

/-- The finite projection formula uniquely characterizes the completed group map. -/
theorem completedBCHToGroupLike_unique (f : d.completedBCHGroup ℒ →* G)
    (hf : ∀ k g, (F).projection k ((f g).val : (F).completion) =
      (truncatedBCHToUnits d ℒ k (CompletedGroup.projection k g) :
        U ⧸ (F).ideal (k + 1))) : f = completedBCHToGroupLike d ℒ := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  exact (F).completion_ext fun k => (hf k g).trans
    (projection_completedBCHToGroupLike d ℒ k g).symm

/-- A group-like unit comes from the completed BCH group exactly when its logarithm
comes from the completed Lie algebra. -/
theorem mem_range_completedBCHToGroupLike_iff (u : G) :
    u ∈ Set.range (completedBCHToGroupLike d ℒ) ↔
      (F).completedLog ⟨(u.val : (F).completion),
        ((mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mp u.property).sub_one_mem
          ℒ d.degree hneg hpos⟩ ∈ Set.range (completedLieToU d ℒ) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨(d.completedBCHExp ℒ).symm g, ?_⟩
    simp only [coe_completedBCHToGroupLike, Mei.AlgFiltration.completedLog_completedExp]
  · rintro ⟨x, hx⟩
    refine ⟨d.completedBCHExp ℒ x, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simp only [coe_completedBCHToGroupLike, Equiv.symm_apply_apply]
    trans (F).completedExp ⟨(F).completedLog ⟨(u.val : (F).completion),
      ((mem_completedGroupLikeSubgroup ℒ d.degree hneg _).mp u.property).sub_one_mem
        ℒ d.degree hneg hpos⟩, (F).completedLog_mem _⟩
    · exact congrArg (F).completedExp (Subtype.ext hx)
    · exact (F).completedExp_completedLog _

/-- Every completed group-like unit is the exponential image of a completed BCH
label, over any commutative rational coefficient algebra. -/
theorem completedBCHToGroupLike_surjective :
    Function.Surjective (completedBCHToGroupLike d ℒ) := by
  intro u
  apply (mem_range_completedBCHToGroupLike_iff d ℒ u).mpr
  apply (mem_range_completedLieToU_iff_isCompletedPrimitive d ℒ _).mpr
  apply (isCompletedPrimitive_completedLog_iff ℒ d.degree _ _).mpr
  exact (mem_completedGroupLikeSubgroup ℒ d.degree _ _).mp u.property

end Mei.UniversalEnvelopingAlgebra
