/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Completion
public import Mei.RingTheory.FilteredAlgebra.Exp

/-!
# Exponentials of completed primitive elements

In a degree-completed enveloping algebra over a commutative rational algebra,
exponentiation identifies primitive elements of the first ideal with group-like
elements congruent to one. For a strictly positive Lie grading, every group-like
element is congruent to one, so logarithms give primitive coordinates on all of them.
No basis, flatness, or finite-dimensionality assumption is needed.

The tensor product is completed for total degree. Its two inclusions commute;
Mathlib's finite exponential addition formula and Tau Ceti's finite logarithm
inverse identities therefore detect the primitive equation at every order.
The construction reuses `Mei.AlgFiltration.completedExpEquiv`.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
/-- Rational scalars on the enveloping algebra induced from its coefficient ring. -/
local instance instAlgebraRatEnveloping : Algebra ℚ U := Algebra.compHom U (algebraMap ℚ R)

local notation "F" => degreeFiltration ℒ d hneg
local notation "T" => Mei.AlgFiltration.tensorProduct R (F) (F)

/-- The completed coproduct commutes with exponentiation on the first ideal. -/
@[simp]
theorem completedCoproduct_completedExp (x : (F).completionIdeal 1) :
    completedCoproduct ℒ d hneg ((F).completedExp x) =
      (T).completedExp ⟨completedCoproduct ℒ d hneg x,
        completedCoproduct_mem_completionIdeal ℒ d hneg 1 x.property⟩ := by
  apply (T).completion_ext
  intro k
  simp only [Mei.AlgFiltration.projection_completedExp, projection_completedCoproduct]
  exact (F).isNilpotent_projection x.property k |>.map_exp
    ((Ideal.Quotient.factor (by rw [Mei.AlgFiltration.tensorProduct_ideal])).comp
      (quotientCoproduct ℒ d hneg (k + 1)).toRingHom)

/-- The exponential of an order-one element is group-like exactly when it is primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (x : (F).completionIdeal 1) :
    IsCompletedGroupLike ℒ d hneg ((F).completedExp x) ↔
      IsCompletedPrimitive ℒ d hneg x := by
  have hx0 : (F).projection 0 x = 0 := by
    simpa only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker] using x.property
  let a : (T).completionIdeal 1 :=
    ⟨(F).includeLeftCompletion (R := R) (F) x, by
      simp only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker,
        Mei.AlgFiltration.projection_includeLeftCompletion, hx0, map_zero]⟩
  let b : (T).completionIdeal 1 :=
    ⟨(F).includeRightCompletion (R := R) (F) x, by
      simp only [Mei.AlgFiltration.completionIdeal_succ, RingHom.mem_ker,
        Mei.AlgFiltration.projection_includeRightCompletion, hx0, map_zero]⟩
  let c : (T).completionIdeal 1 :=
    ⟨completedCoproduct ℒ d hneg x,
      completedCoproduct_mem_completionIdeal ℒ d hneg 1 x.property⟩
  have hΔ : completedCoproduct ℒ d hneg ((F).completedExp x) = (T).completedExp c :=
    completedCoproduct_completedExp ℒ d hneg x
  have hleft : (F).includeLeftCompletion (R := R) (F) ((F).completedExp x) =
      (T).completedExp a := by
    apply (T).completion_ext
    intro k
    simp only [a, Mei.AlgFiltration.projection_includeLeftCompletion,
      Mei.AlgFiltration.projection_completedExp]
    exact (F).isNilpotent_projection x.property k |>.map_exp _
  have hright : (F).includeRightCompletion (R := R) (F) ((F).completedExp x) =
      (T).completedExp b := by
    apply (T).completion_ext
    intro k
    simp only [b, Mei.AlgFiltration.projection_includeRightCompletion,
      Mei.AlgFiltration.projection_completedExp]
    exact (F).isNilpotent_projection x.property k |>.map_exp _
  have hab : Commute (a : (T).completion) b :=
    (F).commute_includeLeftCompletion_includeRightCompletion (R := R) (F) x x
  have hcounit : completedCounit ℒ d hneg ((F).completedExp x) = 1 := by
    have h := completedCounit_eq_zero_of_mem ℒ d hneg ((F).completedExp_sub_one_mem x)
    simpa only [map_sub, map_one, sub_eq_zero] using h
  rw [isCompletedGroupLike_iff, hcounit, eq_self, true_and,
    Mei.AlgFiltration.completedTensor_apply, hΔ, hleft, hright,
    ← (T).completedExp_add a b hab,
    isCompletedPrimitive_iff, Mei.AlgFiltration.completedTensor_one_right,
    Mei.AlgFiltration.completedTensor_one_left]
  constructor
  · intro h
    have he : c = a + b := (T).completedExpEquiv.injective (Subtype.ext (by
      simpa only [Mei.AlgFiltration.coe_completedExpEquiv] using h))
    exact congrArg Subtype.val he
  · intro h
    exact congrArg (T).completedExp (Subtype.ext h)

/-- A logarithm is primitive exactly when its argument is group-like. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff
    (u : {u : (F).completion // u - 1 ∈ (F).completionIdeal 1}) :
    IsCompletedPrimitive ℒ d hneg ((F).completedLog u) ↔
      IsCompletedGroupLike ℒ d hneg u := by
  simpa only [Mei.AlgFiltration.completedExp_completedLog] using
    (isCompletedGroupLike_completedExp_iff ℒ d hneg
      ⟨(F).completedLog u, (F).completedLog_mem u⟩).symm

/-- For a strictly positive grading, exponential and logarithm identify order-one
primitive elements with all completed group-like elements. -/
noncomputable def completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x} ≃
      {u : (F).completion // IsCompletedGroupLike ℒ d hneg u} :=
  ((F).completedExpEquiv.subtypeEquiv
    (fun x => by
      simpa only [Mei.AlgFiltration.coe_completedExpEquiv] using
        (isCompletedGroupLike_completedExp_iff ℒ d hneg x).symm)).trans
    (Equiv.subtypeSubtypeEquivSubtype
      (fun hu => hu.sub_one_mem ℒ d hneg hpos))

/-- The primitive exponential equivalence evaluates by the completed exponential. -/
@[simp]
theorem coe_completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (x : {x : (F).completionIdeal 1 // IsCompletedPrimitive ℒ d hneg x}) :
    (completedPrimitiveExpEquiv ℒ d hneg hpos x).val = (F).completedExp x.val := by
  simp only [completedPrimitiveExpEquiv, Equiv.trans_apply,
    Equiv.subtypeSubtypeEquivSubtype_apply_coe, Equiv.coe_subtypeEquiv_eq_map,
    Subtype.map, Mei.AlgFiltration.coe_completedExpEquiv]

/-- The inverse primitive exponential equivalence evaluates by the completed logarithm. -/
@[simp]
theorem coe_completedPrimitiveExpEquiv_symm (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : {u : (F).completion // IsCompletedGroupLike ℒ d hneg u}) :
    ((completedPrimitiveExpEquiv ℒ d hneg hpos).symm u).val.val =
      (F).completedLog ⟨u.val, u.property.sub_one_mem ℒ d hneg hpos⟩ := by
  have h : (F).completedExpEquiv
      ((completedPrimitiveExpEquiv ℒ d hneg hpos).symm u).val =
        ⟨u.val, u.property.sub_one_mem ℒ d hneg hpos⟩ := by
    apply Subtype.ext
    rw [Mei.AlgFiltration.coe_completedExpEquiv]
    simpa only [Equiv.apply_symm_apply] using
      (coe_completedPrimitiveExpEquiv ℒ d hneg hpos
        ((completedPrimitiveExpEquiv ℒ d hneg hpos).symm u)).symm
  simpa only [Mei.AlgFiltration.coe_completedExpEquiv_symm] using
    congrArg Subtype.val ((F).completedExpEquiv.eq_symm_apply.mpr h)

end Mei.UniversalEnvelopingAlgebra
