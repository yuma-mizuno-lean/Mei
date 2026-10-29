/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Enveloping
public import Mei.Algebra.Lie.Filtered.Module
public import Mei.Algebra.Lie.Filtered.Faithful
public import Mei.Algebra.Lie.UniversalEnveloping.BCH.Basic
public import Mei.Algebra.Lie.BCH.Coordinates
public import Mei.LinearAlgebra.ModuleFiltration.GroupAction
public import Mei.RingTheory.FilteredAlgebra.Action

/-!
# Completed BCH actions on filtered coefficients

A filtration-raising Lie action integrates to a representation of the completed
BCH group on the completed coefficient module, and by algebra automorphisms
when the Lie action is by derivations. Its finite components are exactly
the existing exponential operators, so their previously established truncation
and coefficient-map laws apply. Filtration detection makes this representation
faithful, without requiring faithful representations at individual orders.

The finite representation composes
`Mei.UniversalEnvelopingAlgebra.truncatedBCHToUnits` with
`Mei.ModuleFiltration.truncatedEnvelopingAction` and Mathlib's general linear group
comparison. `ModuleFiltration.completedAction` assembles its inverse limit.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Mei.ModuleFiltration

open Mei.UniversalEnvelopingAlgebra

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- Rational scalars on the enveloping algebra come from the coefficient ring. -/
local instance rationalEnvelopingAlgebra :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra R L) :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- The finite coefficient module inherits rational scalars from `R`. -/
local instance quotientRatModuleBCH (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- The finite BCH representation on the coefficient quotient of the same order. -/
noncomputable def truncatedBCHAction (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) →* (F.quotient k ≃ₗ[R] F.quotient k) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (F.quotient k)).toMonoidHom.comp
    ((Units.map (F.truncatedEnvelopingAction d ℒ k).toMonoidHom).comp
      (truncatedBCHToUnits d ℒ k))

/-- The finite BCH representation is the exponential of the truncated Lie representation. -/
@[simp]
theorem truncatedBCHAction_apply (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (a : F.quotient k) :
    F.truncatedBCHAction d ℒ k g a =
      F.truncatedExpLieAction d ℒ k (BCHGroup.log g) a := by
  have hn : IsNilpotent (truncatedLieToU d ℒ k (BCHGroup.log g)) :=
    ⟨k + 1, truncatedLieToU_pow_eq_zero d ℒ k _⟩
  simp only [truncatedBCHAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Units.coe_map,
    coe_truncatedBCHToUnits, truncatedExpLieAction_apply]
  exact congrArg (fun f : Module.End R (F.quotient k) => f a)
    ((hn.map_exp (F.truncatedEnvelopingAction d ℒ k).toRingHom).trans
      (congrArg IsNilpotent.exp
        (F.truncatedEnvelopingAction_truncatedLieToU d ℒ k (BCHGroup.log g))))

/-- The finite BCH representations commute with both group and coefficient truncation. -/
theorem transition_truncatedBCHAction {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.truncatedLie ℒ l)) (a : F.quotient l) :
    F.transition h (F.truncatedBCHAction d ℒ l g a) =
      F.truncatedBCHAction d ℒ k ((d.truncationMap ℒ h).bchGroupMap g)
        (F.transition h a) := by
  simp only [truncatedBCHAction_apply, LieHom.log_bchGroupMap,
    transition_truncatedExpLieAction]

/-- The completed BCH group acts linearly on the completion of a filtered Lie module. -/
noncomputable def completedBCHAction :
    d.completedBCHGroup ℒ →* (F.completion ≃ₗ[R] F.completion) :=
  F.completedAction (F.truncatedBCHAction d ℒ)
    (fun {_ _} h g a => F.transition_truncatedBCHAction d ℒ h g a)

/-- Each component depends only on the group and coefficient components at that order. -/
@[simp]
theorem projection_completedBCHAction (g : d.completedBCHGroup ℒ)
    (a : F.completion) (k : ℕ) :
    F.projection k (F.completedBCHAction d ℒ g a) =
      F.truncatedBCHAction d ℒ k (CompletedGroup.projection k g) (F.projection k a) := by
  exact F.projection_completedAction _ _ g a k

/-- The integrated action agrees with the existing exponential operator in Lie coordinates. -/
@[simp]
theorem completedBCHAction_exp (x : d.completedLie ℒ) :
    F.completedBCHAction d ℒ (d.completedBCHExp ℒ x) =
      F.completedExpLieAction d ℒ x := by
  apply LinearEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  simp

/-- The finite projection law uniquely determines the completed BCH representation. -/
theorem completedBCHAction_unique
    (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₗ[R] F.completion))
    (hσ : ∀ g a k, F.projection k (σ g a) =
      F.truncatedBCHAction d ℒ k (CompletedGroup.projection k g) (F.projection k a)) :
    σ = F.completedBCHAction d ℒ :=
  F.completedAction_unique _ _ σ hσ

/-- A filtration-detected Lie action integrates to a faithful completed BCH representation. -/
theorem completedBCHAction_injective [IsFiltrationDetected d ℒ F] :
    Function.Injective (F.completedBCHAction d ℒ) := by
  intro g h hgh
  obtain ⟨x, rfl⟩ := (d.completedBCHExp ℒ).surjective g
  obtain ⟨y, rfl⟩ := (d.completedBCHExp ℒ).surjective h
  congr 1
  apply F.eq_of_exp_truncatedLieAction_eq d ℒ x y
  intro k
  apply LinearMap.ext
  intro a
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  have he := congrArg (fun e => F.projection k (e (F.of m))) hgh
  simpa only [projection_completedBCHAction, PositiveDegrees.projection_completedBCHExp,
    truncatedBCHAction_apply, BCHGroup.log_exp, truncatedExpLieAction_apply,
    projection_of, Submodule.mkQ_apply] using he

end Mei.ModuleFiltration

namespace Mei.AlgFiltration

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [Algebra ℚ A] [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]

/-- Rational scalars on the module quotient are induced from `R`. -/
local instance rationalModuleQuotient (k : ℕ) :
    Module ℚ ((F.toModuleFiltration R).quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The module and algebra quotient exponentials agree under the canonical quotient comparison. -/
theorem truncatedExpLieAction_restrictScalarsEquiv (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : (F.toModuleFiltration R).quotient k) :
    F.truncatedExpLieAction d ℒ k x
        (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1)) a) =
      Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
        ((F.toModuleFiltration R).truncatedExpLieAction d ℒ k x a) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  let e := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
  have hc : (F.quotientLieAction d ℒ k x).comp e.toLinearMap =
      e.toLinearMap.comp ((F.toModuleFiltration R).quotientLieAction d ℒ k x) := by
    apply LinearMap.ext
    intro a
    obtain ⟨a, rfl⟩ := ((F.toModuleFiltration R).submodule (k + 1)).mkQ_surjective a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply, e,
      Submodule.Quotient.restrictScalarsEquiv_mk]
    rw [Ideal.Quotient.mk_eq_mk, quotientLieAction_mk,
      (F.toModuleFiltration R).quotientLieAction_mk d ℒ k x a]
    rfl
  simpa only [LieIdeal.mkQ_apply, truncatedExpLieAction_mk,
    quotientExpLieAction_apply, ModuleFiltration.truncatedExpLieAction_apply,
    ModuleFiltration.truncatedLieAction_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, e] using
    LinearMap.congr_fun (Module.End.commute_exp_left_of_commute
      ((F.toModuleFiltration R).isNilpotent_quotientLieAction d ℒ k x)
      ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩ hc) a

/-- The finite BCH group acts on each coefficient quotient by algebra automorphisms. -/
noncomputable def truncatedBCHAction (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) →*
      ((A ⧸ F.ideal (k + 1)) ≃ₐ[R] (A ⧸ F.ideal (k + 1))) where
  toFun g := F.truncatedExpLieAction d ℒ k (BCHGroup.log g)
  map_one' := by
    apply AlgEquiv.ext
    intro a
    simp
  map_mul' g h := by
    apply AlgEquiv.ext
    intro a
    let e := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
    obtain ⟨a, rfl⟩ := e.surjective a
    have he := congrArg (fun f : (F.toModuleFiltration R).quotient k ≃ₗ[R]
        (F.toModuleFiltration R).quotient k => e (f a))
      (((F.toModuleFiltration R).truncatedBCHAction d ℒ k).map_mul g h)
    simpa only [LinearEquiv.mul_apply, ModuleFiltration.truncatedBCHAction_apply,
      ← truncatedExpLieAction_restrictScalarsEquiv, AlgEquiv.mul_apply, e] using he

/-- The finite algebra action is the already constructed truncated exponential. -/
@[simp]
theorem truncatedBCHAction_apply (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (a : A ⧸ F.ideal (k + 1)) :
    F.truncatedBCHAction d ℒ k g a =
      F.truncatedExpLieAction d ℒ k (BCHGroup.log g) a := (rfl)

/-- Coefficient truncation intertwines the finite BCH algebra actions. -/
theorem factor_truncatedBCHAction {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.truncatedLie ℒ l)) (a : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (F.truncatedBCHAction d ℒ l g a) =
      F.truncatedBCHAction d ℒ k ((d.truncationMap ℒ h).bchGroupMap g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) a) := by
  rw [truncatedBCHAction_apply, truncatedBCHAction_apply, LieHom.log_bchGroupMap]
  exact F.factor_truncatedExpLieAction d ℒ h (BCHGroup.log g) a

/-- Integrate a filtration-raising derivation action to the completed BCH group. -/
noncomputable def completedBCHAction :
    d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion) :=
  F.completedAction (F.truncatedBCHAction d ℒ)
    (fun {_ _} h g a => F.factor_truncatedBCHAction d ℒ h g a)

/-- The completed algebra action is computed by exponential operators at each finite order. -/
@[simp]
theorem projection_completedBCHAction (g : d.completedBCHGroup ℒ)
    (a : F.completion) (k : ℕ) :
    F.projection k (F.completedBCHAction d ℒ g a) =
      F.truncatedExpLieAction d ℒ k (BCHGroup.log (CompletedGroup.projection k g))
        (F.projection k a) := by
  exact F.projection_completedAction _ _ g a k

/-- The finite-order projection law uniquely determines the completed algebra action. -/
theorem completedBCHAction_unique
    (σ : d.completedBCHGroup ℒ →* (F.completion ≃ₐ[R] F.completion))
    (hσ : ∀ g a k, F.projection k (σ g a) =
      F.truncatedExpLieAction d ℒ k (BCHGroup.log (CompletedGroup.projection k g))
        (F.projection k a)) : σ = F.completedBCHAction d ℒ :=
  F.completedAction_unique _ _ σ hσ

/-- Completed algebra actions agreeing on the canonical image of `A` agree: every completed
element has the same finite-order projections as a canonical one. -/
theorem completedBCHAction_eq_of_forall_toCompletion {g h : d.completedBCHGroup ℒ}
    (hgh : ∀ a : A, F.completedBCHAction d ℒ g (F.toCompletion a) =
      F.completedBCHAction d ℒ h (F.toCompletion a)) :
    F.completedBCHAction d ℒ g = F.completedBCHAction d ℒ h := by
  apply AlgEquiv.ext
  intro z
  apply F.completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k z)
  have hk := congrArg (F.projection k) (hgh a)
  simp only [projection_completedBCHAction, projection_toCompletion] at hk ⊢
  rw [← ha]
  exact hk

/-- Filtration detection makes the completed action by algebra automorphisms faithful. -/
theorem completedBCHAction_injective
    [IsFiltrationDetected d ℒ (F.toModuleFiltration R)] :
    Function.Injective (F.completedBCHAction d ℒ) := by
  intro g h hgh
  obtain ⟨x, rfl⟩ := (d.completedBCHExp ℒ).surjective g
  obtain ⟨y, rfl⟩ := (d.completedBCHExp ℒ).surjective h
  congr 1
  apply (F.toModuleFiltration R).eq_of_exp_truncatedLieAction_eq d ℒ x y
  intro k
  apply LinearMap.ext
  intro a
  obtain ⟨m, rfl⟩ := ((F.toModuleFiltration R).submodule (k + 1)).mkQ_surjective a
  apply (Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))).injective
  have he := congrArg (fun e => F.projection k (e (F.toCompletion m))) hgh
  simpa only [projection_completedBCHAction, PositiveDegrees.projection_completedBCHExp,
    BCHGroup.log_exp, projection_toCompletion,
    ← ModuleFiltration.truncatedExpLieAction_apply,
    ← truncatedExpLieAction_restrictScalarsEquiv,
    Submodule.Quotient.restrictScalarsEquiv_mk, Submodule.mkQ_apply,
    Ideal.Quotient.mk_eq_mk] using he

/-- On original Lie elements, the completed group action is the existing exponential action. -/
@[simp]
theorem completedBCHAction_exp (x : L) :
    F.completedBCHAction d ℒ (d.expToCompletion ℒ x) = F.expAction d ℒ x := by
  apply AlgEquiv.ext
  intro a
  apply F.completion_ext
  intro k
  simp

end Mei.AlgFiltration
