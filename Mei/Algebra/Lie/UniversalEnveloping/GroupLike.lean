/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Exp
public import Mathlib.Algebra.Group.Submonoid.Units

/-!
# The group of completed group-like elements

Group-like units of a degree-completed enveloping algebra form a subgroup.
For a strictly positive grading over a rational algebra, every group-like element
is a unit, so the subgroup accounts for the entire group-like submonoid.
Exponential coordinates identify this subgroup with the primitive elements of the
first completion ideal; inversion corresponds to negation.

The subgroup construction uses Mathlib's `MonoidHom.eqLocus` and `MonoidHom.ker`:
the coproduct and the tensor-square map are monoid homomorphisms on units, and
the counit must equal one. In particular, inverse closure requires neither
rational coefficients nor positivity. The unit theorem uses Mei's completed
exponential and logarithm and their inverse identities.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R]
  [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "F" => degreeFiltration ℒ d hneg
local notation "T" => Mei.AlgFiltration.tensorProduct R
  (degreeFiltration ℒ d hneg) (degreeFiltration ℒ d hneg)

/-- The subgroup of units whose counit is one and whose completed coproduct
is their tensor square. -/
noncomputable def completedGroupLikeSubgroup : Subgroup (F).completionˣ :=
  let diagonal : (F).completionˣ →* (T).completion :=
    { toFun := fun u => (F).completedTensor (R := R) (F) u u
      map_one' := by simp
      map_mul' := fun u v => (F).completedTensor_mul (F) u v u v }
  ((completedCoproduct ℒ d hneg).toMonoidHom.comp (Units.coeHom _)).eqLocus diagonal ⊓
    ((completedCounit ℒ d hneg).toMonoidHom.comp (Units.coeHom _)).ker

/-- Membership in the subgroup is precisely the group-like condition on the value. -/
@[simp]
theorem mem_completedGroupLikeSubgroup (u : (F).completionˣ) :
    u ∈ completedGroupLikeSubgroup ℒ d hneg ↔
      IsCompletedGroupLike ℒ d hneg (u : (F).completion) := by
  simp [completedGroupLikeSubgroup, MonoidHom.eqLocus, MonoidHom.mem_eqLocusM,
    isCompletedGroupLike_iff, and_comm]

/-- The inverse of a group-like unit is group-like. -/
theorem IsCompletedGroupLike.inv {u : (F).completionˣ}
    (hu : IsCompletedGroupLike ℒ d hneg (u : (F).completion)) :
    IsCompletedGroupLike ℒ d hneg (u⁻¹ : (F).completionˣ) := by
  exact (mem_completedGroupLikeSubgroup ℒ d hneg u⁻¹).mp
    ((completedGroupLikeSubgroup ℒ d hneg).inv_mem
      ((mem_completedGroupLikeSubgroup ℒ d hneg u).mpr hu))

section Rational

variable [Algebra ℚ R]

/-- Rational scalars act through the coefficient ring on the enveloping algebra. -/
local instance rationalGroupLikeEnvelopingAlgebra :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra R L) :=
  Algebra.compHom _ (algebraMap ℚ R)

variable (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)

include hpos

/-- Every completed group-like element is invertible for a strictly positive grading. -/
theorem IsCompletedGroupLike.isUnit {u : (F).completion}
    (hu : IsCompletedGroupLike ℒ d hneg u) : IsUnit u := by
  let v : {v : (F).completion // v - 1 ∈ (F).completionIdeal 1} :=
    ⟨u, hu.sub_one_mem ℒ d hneg hpos⟩
  simpa only [Mei.AlgFiltration.completedExp_completedLog] using
    (F).isUnit_completedExp ⟨(F).completedLog v, (F).completedLog_mem v⟩

/-- Forgetting that group-like units are units recovers all group-like elements. -/
theorem completedGroupLikeSubgroup_ofUnits :
    (completedGroupLikeSubgroup ℒ d hneg).ofUnits =
      completedGroupLikeSubmonoid ℒ d hneg := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_completedGroupLikeSubmonoid ℒ d hneg _).mpr
      ((mem_completedGroupLikeSubgroup ℒ d hneg v).mp hv)
  · intro hu
    have hg := (mem_completedGroupLikeSubmonoid ℒ d hneg u).mp hu
    have hunit := hg.isUnit ℒ d hneg hpos
    exact ⟨hunit.unit, (mem_completedGroupLikeSubgroup ℒ d hneg _).mpr
      (by simpa only [hunit.unit_spec] using hg), hunit.unit_spec⟩

/-- The group-like submonoid is multiplicatively equivalent to the subgroup of
group-like units. -/
noncomputable def completedGroupLikeEquivUnits :
    completedGroupLikeSubmonoid ℒ d hneg ≃*
      completedGroupLikeSubgroup ℒ d hneg :=
  (MulEquiv.submonoidCongr (completedGroupLikeSubgroup_ofUnits ℒ d hneg hpos).symm).trans
    (completedGroupLikeSubgroup ℒ d hneg).ofUnitsEquivType

/-- The group-like equivalence preserves the value in the completed algebra. -/
@[simp]
theorem coe_completedGroupLikeEquivUnits
    (u : completedGroupLikeSubmonoid ℒ d hneg) :
    ((completedGroupLikeEquivUnits ℒ d hneg hpos u).val : (F).completion) = u :=
  (Subgroup.unit_of_mem_ofUnits_spec_val_eq_of_mem _ _)

/-- The inverse equivalence forgets the unit structure. -/
@[simp]
theorem coe_completedGroupLikeEquivUnits_symm
    (u : completedGroupLikeSubgroup ℒ d hneg) :
    ((completedGroupLikeEquivUnits ℒ d hneg hpos).symm u : (F).completion) = u.val :=
  (rfl)

/-- Exponential coordinates for the subgroup of completed group-like units. -/
noncomputable def completedPrimitiveExpUnitsEquiv :
    {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x} ≃
      completedGroupLikeSubgroup ℒ d hneg :=
  (completedPrimitiveExpEquiv ℒ d hneg hpos).trans
    ((Equiv.subtypeEquivRight fun u =>
      (mem_completedGroupLikeSubmonoid ℒ d hneg u).symm).trans
        (completedGroupLikeEquivUnits ℒ d hneg hpos).toEquiv)

/-- The subgroup-valued exponential has the usual completed exponential as value. -/
@[simp]
theorem coe_completedPrimitiveExpUnitsEquiv
    (x : {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x}) :
    ((completedPrimitiveExpUnitsEquiv ℒ d hneg hpos x).val : (F).completion) =
      (F).completedExp x.val := by
  simp [completedPrimitiveExpUnitsEquiv]

/-- The inverse exponential coordinate is the completed logarithm. -/
@[simp]
theorem coe_completedPrimitiveExpUnitsEquiv_symm
    (u : completedGroupLikeSubgroup ℒ d hneg) :
    (((completedPrimitiveExpUnitsEquiv ℒ d hneg hpos).symm u).val : (F).completion) =
      (F).completedLog ⟨u.val,
        ((mem_completedGroupLikeSubgroup ℒ d hneg _).mp u.property).sub_one_mem
          ℒ d hneg hpos⟩ := by
  simp [completedPrimitiveExpUnitsEquiv]

/-- Negating a primitive exponential coordinate gives the inverse group-like unit. -/
theorem completedPrimitiveExpUnitsEquiv_neg
    (x : {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x}) :
    completedPrimitiveExpUnitsEquiv ℒ d hneg hpos
        ⟨-x.val, (mem_completedPrimitives ℒ d hneg _).mp
          ((completedPrimitives ℒ d hneg).neg_mem
            ((mem_completedPrimitives ℒ d hneg _).mpr x.property))⟩ =
      (completedPrimitiveExpUnitsEquiv ℒ d hneg hpos x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_completedPrimitiveExpUnitsEquiv,
    Subgroup.coe_one, Units.val_one]
  exact (F).completedExp_neg_mul_completedExp x.val

end Rational

end Mei.UniversalEnvelopingAlgebra
