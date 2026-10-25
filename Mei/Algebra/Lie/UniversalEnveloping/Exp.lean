/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Completion
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Exp

/-!
# Exponentiating completed primitive elements

In the degree completion of an enveloping algebra over a commutative rational
algebra, exponential and logarithm exchange primitive elements of the first
filtration ideal and group-like elements congruent to one. For a strictly
positive Lie grading every group-like element is congruent to one, so this gives
an equivalence with all completed group-like elements.

The coproduct is valued in the total-degree tensor completion. Mathlib's
`IsNilpotent.map_exp` and commutation of the completed tensor inclusions give
the exponential identity at every finite order. Injectivity of Mei's
`AlgFiltration.completedExpEquiv` gives its converse. No PBW theorem, freeness,
or finite-dimensionality is required.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d hneg
local notation "T" => Mei.AlgFiltration.tensorProduct R
  (degreeFiltration ℒ d hneg) (degreeFiltration ℒ d hneg)

/-- Restrict the scalar algebra through the rational structure on the coefficient ring. -/
local instance rationalEnvelopingAlgebra : Algebra ℚ U :=
  Algebra.compHom U (algebraMap ℚ R)

/-- The completed enveloping coproduct commutes with exponentiation. -/
theorem completedCoproduct_completedExp (x : (F).completionIdeal 1) :
    completedCoproduct ℒ d hneg ((F).completedExp x) =
      (T).completedExp ⟨completedCoproduct ℒ d hneg x,
        completedCoproduct_mem_completionIdeal ℒ d hneg 1 x.property⟩ := by
  apply (T).completion_ext
  intro k
  simp only [projection_completedCoproduct, Mei.AlgFiltration.projection_completedExp]
  exact ((F).isNilpotent_projection x.property k).map_exp
    ((Ideal.Quotient.factor (by rw [Mei.AlgFiltration.tensorProduct_ideal])).comp
      (quotientCoproduct ℒ d hneg (k + 1)).toRingHom)

/-- A completed exponential has counit one. -/
@[simp]
theorem completedCounit_completedExp (x : (F).completionIdeal 1) :
    completedCounit ℒ d hneg ((F).completedExp x) = 1 := by
  have hx : (F).projection 0 x = 0 := by
    simpa only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker] using x.property
  rw [completedCounit_eq_quotientCounit ℒ d hneg 0,
    Mei.AlgFiltration.projection_completedExp, hx, IsNilpotent.exp_zero, map_one]

/-- An element of the first ideal is primitive exactly when its exponential is group-like. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (x : (F).completionIdeal 1) :
    IsCompletedGroupLike ℒ d hneg ((F).completedExp x) ↔
      IsCompletedPrimitive ℒ d hneg x := by
  let a : (T).completionIdeal 1 :=
    ⟨(F).includeLeftCompletion (R := R) (F) x,
      (F).includeLeftCompletion_mem_completionIdeal (F) x.property⟩
  let b : (T).completionIdeal 1 :=
    ⟨(F).includeRightCompletion (R := R) (F) x,
      (F).includeRightCompletion_mem_completionIdeal (F) x.property⟩
  let c : (T).completionIdeal 1 :=
    ⟨completedCoproduct ℒ d hneg x,
      completedCoproduct_mem_completionIdeal ℒ d hneg 1 x.property⟩
  simp only [isCompletedGroupLike_iff, isCompletedPrimitive_iff,
    Mei.AlgFiltration.completedTensor_one_right, Mei.AlgFiltration.completedTensor_one_left,
    completedCounit_completedExp,
    true_and, completedCoproduct_completedExp, Mei.AlgFiltration.completedTensor_completedExp]
  constructor
  · intro h
    have hab : c = a + b := by
      apply (T).completedExpEquiv.injective
      apply Subtype.ext
      simpa only [Mei.AlgFiltration.coe_completedExpEquiv] using h
    exact congrArg Subtype.val hab
  · intro h
    exact congrArg (T).completedExp (Subtype.ext h)

/-- The logarithm of an element congruent to one is primitive exactly when that element
is group-like. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff
    (u : {u : (F).completion // u - 1 ∈ (F).completionIdeal 1}) :
    IsCompletedPrimitive ℒ d hneg ((F).completedLog u) ↔
      IsCompletedGroupLike ℒ d hneg u := by
  simpa only [Mei.AlgFiltration.completedExp_completedLog] using
    (isCompletedGroupLike_completedExp_iff ℒ d hneg
      ⟨(F).completedLog u, (F).completedLog_mem u⟩).symm

omit [Algebra ℚ R] in
/-- For a strictly positive Lie grading, the first completion ideal is precisely
the kernel of the completed counit. -/
theorem mem_completionIdeal_one_iff_counit_eq_zero
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : (F).completion) :
    x ∈ (F).completionIdeal 1 ↔ completedCounit ℒ d hneg x = 0 := by
  refine ⟨completedCounit_eq_zero_of_mem ℒ d hneg, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((F).projection 0 x)
  have hc : Coalgebra.counit (R := R) a = 0 := by
    rw [completedCounit_eq_quotientCounit ℒ d hneg 0, ← ha, quotientCounit_mk] at hx
    exact hx
  have hm : a ∈ (F).ideal 1 := augmentation_le_degreeFiltration_one ℒ d hpos
    ((TauCeti.HopfIdeal.mem_augmentation R _).mpr hc)
  simpa only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker,
    ← ha, Ideal.Quotient.eq_zero_iff_mem] using hm

omit [Algebra ℚ R] in
/-- Every completed group-like element is congruent to one for a strictly positive grading. -/
theorem IsCompletedGroupLike.sub_one_mem
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) {u : (F).completion}
    (hu : IsCompletedGroupLike ℒ d hneg u) :
    u - 1 ∈ (F).completionIdeal 1 := by
  have hc := ((isCompletedGroupLike_iff ℒ d hneg u).mp hu).1
  rw [mem_completionIdeal_one_iff_counit_eq_zero ℒ d hneg hpos, map_sub, map_one,
    hc, sub_self]

/-- Exponential coordinates identify the primitive elements in the first ideal
with all completed group-like elements of a strictly positively graded enveloping algebra. -/
noncomputable def completedPrimitiveExpEquiv
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x} ≃
      {u : (F).completion // IsCompletedGroupLike ℒ d hneg u} where
  toFun x := ⟨(F).completedExp x.val,
    (isCompletedGroupLike_completedExp_iff ℒ d hneg x.val).mpr x.property⟩
  invFun u := ⟨⟨(F).completedLog ⟨u.val, u.property.sub_one_mem ℒ d hneg hpos⟩,
    (F).completedLog_mem _⟩,
    (isCompletedPrimitive_completedLog_iff ℒ d hneg _).mpr u.property⟩
  left_inv x := Subtype.ext (Subtype.ext ((F).completedLog_completedExp x.val))
  right_inv u := Subtype.ext ((F).completedExp_completedLog
    ⟨u.val, u.property.sub_one_mem ℒ d hneg hpos⟩)

/-- The primitive-to-group-like equivalence is given by the completed exponential. -/
@[simp]
theorem coe_completedPrimitiveExpEquiv
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (x : {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x}) :
    (completedPrimitiveExpEquiv ℒ d hneg hpos x : (F).completion) =
      (F).completedExp x.val := (rfl)

/-- The inverse primitive-to-group-like equivalence is given by the completed logarithm. -/
@[simp]
theorem coe_completedPrimitiveExpEquiv_symm
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : {u : (F).completion // IsCompletedGroupLike ℒ d hneg u}) :
    ((completedPrimitiveExpEquiv ℒ d hneg hpos).symm u : (F).completion) =
      (F).completedLog ⟨u.val, u.property.sub_one_mem ℒ d hneg hpos⟩ := (rfl)

end Mei.UniversalEnvelopingAlgebra
