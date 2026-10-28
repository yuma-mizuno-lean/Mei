/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Grading.Lie
public import Mei.Algebra.Lie.BCH.Ray.Single

/-!
# Charge-one ray groups of module probes

A supported module ray has at most one nonzero homogeneous piece: its charge-one
coefficient piece. Higher multiples have charge at least two and vanish. Its
completed ray subgroup is therefore precisely the exponential of that coefficient
module, with multiplication given by addition of coefficients.

This identifies ray labels in the semidirect module probe with homogeneous
coefficients. The coefficient module uses the original shifted support, so no
saturation or nonzero spatial direction is required. The semidirect probe setting
is that of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183). The group comparison specializes
`PositiveDegrees.completedRaySingleEquiv`.
-/

public section

noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

/-- A piece on a module ray vanishes unless it is the charge-one generator piece. -/
theorem grading_eq_bot_of_charge_one_ray (w : SupportedRay (positiveDegrees d p))
    {q : Γ} (hw : w.generator = (q, 1, 0))
    {a : Γ × ℤ × ℤ} (ha : a ∈ w.rayDegrees)
    (hne : a ≠ (q, 1, 0)) : grading d ℳ p ℒ a = ⊥ := by
  obtain ⟨_, c, hc, rfl⟩ := SupportedRay.mem_rayDegrees.mp ha
  rw [hw]
  rw [hw] at hne
  have hc₁ : c ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  simpa only [Prod.smul_mk, smul_zero, zsmul_eq_mul,
    Int.cast_id, mul_one] using
    grading_charge_eq_bot d ℳ p ℒ (c • q) c 0 (by omega) hc₁

/-- The coefficient inclusion identifies its homogeneous piece with the
charge-one homogeneous piece of the probe. -/
def moduleGradingEquiv (q : Γ) :
    shiftedGrading ℳ d.monoid p (q - p) ≃ₗ[R] grading d ℳ p ℒ (q, 1, 0) :=
  (Submodule.equivMapOfInjective
    ((moduleInclusion d ℳ p ℒ).toLinearMap.comp
      (moduleCoefficientsEquiv d ℳ p).symm.toLinearMap)
    ((LieAlgebra.SemiDirectSum.inl_injective _).comp
      (moduleCoefficientsEquiv d ℳ p).symm.injective)
    (shiftedGrading ℳ d.monoid p (q - p))).trans
    (LinearEquiv.ofEq _ _ (grading_module d ℳ p ℒ q).symm)

/-- The homogeneous equivalence is the coefficient inclusion on ambient values. -/
@[simp]
theorem coe_moduleGradingEquiv (q : Γ)
    (a : shiftedGrading ℳ d.monoid p (q - p)) :
    (moduleGradingEquiv d ℳ p ℒ q a : ProbeLie d ℳ p ℒ) =
      moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a.val) := (rfl)

/-- The inverse homogeneous equivalence recovers the shifted coefficient part. -/
@[simp]
theorem coe_moduleGradingEquiv_symm (q : Γ) (x : grading d ℳ p ℒ (q, 1, 0)) :
    ((moduleGradingEquiv d ℳ p ℒ q).symm x : shiftedSubmodule ℳ d.monoid p) =
      moduleCoefficientsEquiv d ℳ p x.val.left := by
  have h := congrArg (fun y : ProbeLie d ℳ p ℒ =>
    moduleCoefficientsEquiv d ℳ p y.left)
    (coe_moduleGradingEquiv d ℳ p ℒ q ((moduleGradingEquiv d ℳ p ℒ q).symm x))
  simpa only [LinearEquiv.apply_symm_apply, moduleInclusion,
    LieAlgebra.SemiDirectSum.inl_eq_mk] using h.symm

section RationalScalars

variable [Algebra ℚ R]

/-- Rational scalars on the probe are induced by its coefficient ring. -/
scoped instance rationalLieAlgebra : LieAlgebra ℚ (ProbeLie d ℳ p ℒ) where
  toModule := Module.compHom _ (algebraMap ℚ R)
  lie_smul r x y := lie_smul (algebraMap ℚ R r) x y

end RationalScalars

variable [SetLike.GradedBracket ℒ ℒ]

/-- The ray Lie algebra of a module ray is exactly its homogeneous coefficient piece. -/
theorem moduleRayLieSubalgebra_toSubmodule (q : Γ) (hq : q - p ∈ d.monoid) :
    (rayLieSubalgebra (grading d ℳ p ℒ) (moduleRay d p q hq)).toSubmodule =
      grading d ℳ p ℒ (q, 1, 0) :=
  rayLieSubalgebra_eq_of_single_degree (grading d ℳ p ℒ)
    (moduleRay d p q hq) (q, 1, 0) (by simp)
    (fun _ ha hne => grading_eq_bot_of_charge_one_ray d ℳ p ℒ (moduleRay d p q hq)
      (moduleRay_generator d p q hq) ha hne)

variable [DirectSum.Decomposition ℳ] [Algebra ℚ R]

/-- If the charge-one generator is not allowed, its entire completed ray group
is trivial, even if higher multiples belong to the positive monoid. -/
theorem completedRaySubgroup_eq_bot_of_notMem (w : SupportedRay (positiveDegrees d p))
    {q : Γ} (hw : w.generator = (q, 1, 0)) (hq : q - p ∉ d.monoid) :
    (positiveDegrees d p).completedRaySubgroup (grading d ℳ p ℒ) w = ⊥ := by
  apply (positiveDegrees d p).completedRaySubgroup_eq_bot_of_rayLieSubalgebra_eq_bot
  apply LieSubalgebra.toSubmodule_injective
  rw [rayLieSubalgebra_toSubmodule, LieSubalgebra.bot_toSubmodule]
  apply iSup_eq_bot.mpr
  intro a
  by_cases ha : (a : Γ × ℤ × ℤ) = (q, 1, 0)
  · rw [ha]
    exact IsPositiveGrading.eq_bot (d := positiveDegrees d p)
      (ℒ := grading d ℳ p ℒ) _ (Or.inl (by simpa using hq))
  · exact grading_eq_bot_of_charge_one_ray d ℳ p ℒ w hw a.property ha

/-- The completed module ray group is the additive homogeneous coefficient group.
No completion of the individual homogeneous piece is needed. -/
def moduleRayGroupEquiv (q : Γ) (hq : q - p ∈ d.monoid) :
    Multiplicative (shiftedGrading ℳ d.monoid p (q - p)) ≃*
      (positiveDegrees d p).completedRaySubgroup (grading d ℳ p ℒ) (moduleRay d p q hq) :=
  (moduleGradingEquiv d ℳ p ℒ q).toAddEquiv.toMultiplicative.trans
    ((positiveDegrees d p).completedRaySingleEquiv (grading d ℳ p ℒ)
      (moduleRay d p q hq) (q, 1, 0) (by simp)
      (fun _ ha hne => grading_eq_bot_of_charge_one_ray d ℳ p ℒ (moduleRay d p q hq)
        (moduleRay_generator d p q hq) ha hne))

/-- The ray equivalence exponentiates the included homogeneous coefficient. -/
@[simp]
theorem coe_moduleRayGroupEquiv (q : Γ) (hq : q - p ∈ d.monoid)
    (a : Multiplicative (shiftedGrading ℳ d.monoid p (q - p))) :
    (moduleRayGroupEquiv d ℳ p ℒ q hq a :
      (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ)) =
      (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a.toAdd.val)) := by
  simp only [moduleRayGroupEquiv, MulEquiv.trans_apply,
    PositiveDegrees.coe_completedRaySingleEquiv]
  rfl

/-- The inverse ray equivalence extracts the homogeneous logarithmic coefficient
and forgets the semidirect inclusion. -/
@[simp]
theorem coe_moduleRayGroupEquiv_symm (q : Γ) (hq : q - p ∈ d.monoid)
    (g : (positiveDegrees d p).completedRaySubgroup (grading d ℳ p ℒ)
      (moduleRay d p q hq)) :
    (((moduleRayGroupEquiv d ℳ p ℒ q hq).symm g).toAdd :
      shiftedSubmodule ℳ d.monoid p) =
      moduleCoefficientsEquiv d ℳ p
        ((positiveDegrees d p).logComponent (grading d ℳ p ℒ) g.val (q, 1, 0)).val.left := by
  simpa only [moduleRayGroupEquiv, MulEquiv.symm_trans_apply,
    PositiveDegrees.completedRaySingleEquiv_symm_apply,
    AddEquiv.toMultiplicative_apply_symm_apply, toAdd_ofAdd,
    ← LinearEquiv.coe_toAddEquiv_symm, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply] using
    coe_moduleGradingEquiv_symm d ℳ p ℒ q
      ((positiveDegrees d p).logComponent (grading d ℳ p ℒ) g.val (q, 1, 0))

end Mei.ModuleProbe
