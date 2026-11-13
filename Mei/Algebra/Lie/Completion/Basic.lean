/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Completion
public import Mathlib.Algebra.Lie.TransferInstance
public import Mei.LinearAlgebra.ModuleFiltration.QuotientTower

/-!
# Lie completions of module filtrations

The module filtration associated to decreasing Lie ideals has the same quotient
tower as TauCeti's Lie completion. Transport its Lie structure to the filtration
completion so that the existing filtration maps can be used on this carrier.
-/

public section

noncomputable section

open TauCeti

namespace Mei.LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I : ℕ → LieIdeal R L) (hI : Antitone I)

/-- The module filtration whose order-`k` quotient is `L ⧸ I k`. -/
-- The terms must compute to identify the module quotients with the Lie quotients.
abbrev completionFiltration : Mei.ModuleFiltration R L where
  submodule
    | 0 => ⊤
    | k + 1 => (I k).toSubmodule
  zero_eq_top := rfl
  antitone := by
    intro k l h
    cases k with
    | zero => exact le_top
    | succ k =>
      cases l with
      | zero => omega
      | succ l => exact hI (Nat.le_of_succ_le_succ h)

/-- Positive-order terms are the original ideals, with scalars retained. -/
@[simp]
theorem completionFiltration_succ (k : ℕ) :
    (completionFiltration I hI).submodule (k + 1) = (I k).toSubmodule := (rfl)

/-- The module transition is the linear map underlying the Lie quotient transition. -/
theorem completionFiltration_transition {k l : ℕ} (h : k ≤ l) :
    (completionFiltration I hI).transition h = (_root_.LieIdeal.factor (hI h)).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (I l).surjective_mkQ x
  simpa only [Mei.ModuleFiltration.transition_mk, LieHom.coe_toLinearMap,
    _root_.LieIdeal.mkQ_apply] using
    (_root_.LieIdeal.factor_apply (hI h) x).symm

/-- Completion along a decreasing sequence of Lie ideals, using the module completion carrier. -/
abbrev completion := (completionFiltration I hI).completion

/-- The module quotient at each order has the Lie structure of the corresponding ideal
quotient. The explicit instance identifies the module-quotient presentation for inference. -/
instance completionQuotientLieRing (k : ℕ) :
    LieRing ((completionFiltration I hI).quotient k) :=
  inferInstanceAs (LieRing (L ⧸ I k))

/-- The scalar action on a finite module quotient is compatible with its Lie bracket. -/
instance completionQuotientLieAlgebra (k : ℕ) :
    LieAlgebra R ((completionFiltration I hI).quotient k) :=
  inferInstanceAs (LieAlgebra R (L ⧸ I k))

/-- The filtration completion identifies with the upstream limit of Lie quotients. -/
def completionEquivLimit : completion I hI ≃ₗ[R] _root_.LieIdeal.completion I hI :=
  (completionFiltration I hI).completionEquivTowerLimit

instance completionLieRing : LieRing (completion I hI) :=
  (completionEquivLimit I hI).toAddEquiv.lieRing

instance completionLieAlgebra : LieAlgebra R (completion I hI) :=
  (completionEquivLimit I hI).lieAlgebra

/-- The quotient-tower comparison is a Lie equivalence. -/
def completionLieEquivLimit : completion I hI ≃ₗ⁅R⁆ _root_.LieIdeal.completion I hI :=
  (completionEquivLimit I hI).lieEquiv R

/-- The underlying linear equivalence is the comparison of quotient-tower limits. -/
theorem completionLieEquivLimit_toLinearEquiv :
    (completionLieEquivLimit I hI).toLinearEquiv =
      (completionFiltration I hI).completionEquivTowerLimit := (rfl)

/-- Projection of the completed bracket is the bracket of the projections. -/
@[simp]
theorem projection_bracket (k : ℕ) (x y : completion I hI) :
    (completionFiltration I hI).projection k ⁅x, y⁆ =
      ⁅((completionFiltration I hI).projection k x : L ⧸ I k),
        ((completionFiltration I hI).projection k y : L ⧸ I k)⁆ := by
  let F := completionFiltration I hI
  let e := completionEquivLimit I hI
  obtain ⟨a, ha⟩ := (I k).surjective_mkQ (F.projection k x)
  obtain ⟨b, hb⟩ := (I k).surjective_mkQ (F.projection k y)
  apply (F.quotientEquivTower k).injective
  have hproj (z : completion I hI) := F.limπ_completionEquivTowerLimit k z
  have ha' : ModuleTower.quotientsπ _ F.quotientAntitone k a = _ :=
    (F.quotientEquivTower_mk k a).symm.trans ((congrArg _ ha).trans (hproj x).symm)
  have hb' : ModuleTower.quotientsπ _ F.quotientAntitone k b = _ :=
    (F.quotientEquivTower_mk k b).symm.trans ((congrArg _ hb).trans (hproj y).symm)
  rw [← hproj, ← ha, ← hb, ← LieHom.map_lie]
  -- The tower projection in `hproj` is evaluated on the linear comparison `e`.
  change (ModuleTower.quotients _ F.quotientAntitone).limπ k (e ⁅x, y⁆) = _
  -- The Lie comparison has the same underlying linear map, so it preserves this bracket.
  rw [show e ⁅x, y⁆ = ⁅e x, e y⁆ from (completionLieEquivLimit I hI).map_lie x y]
  rw [_root_.LieIdeal.limπ_bracket_of_representatives I hI k (e x) (e y) a b ha' hb']
  exact (F.quotientEquivTower_mk k ⁅a, b⁆).symm

/-- The projection to a finite Lie quotient. -/
def completionProjection (k : ℕ) : completion I hI →ₗ⁅R⁆ L ⧸ I k where
  __ := (completionFiltration I hI).projection k
  map_lie' := projection_bracket I hI k _ _

/-- The Lie projection has the existing module projection as its underlying linear map. -/
@[simp]
theorem completionProjection_toLinearMap (k : ℕ) :
    (completionProjection I hI k).toLinearMap = (completionFiltration I hI).projection k :=
  (rfl)

/-- The Lie projection evaluates by the module projection. -/
theorem completionProjection_apply (k : ℕ) (x : completion I hI) :
    completionProjection I hI k x = (completionFiltration I hI).projection k x := (rfl)

/-- Lie projections commute with all quotient transitions. -/
@[simp]
theorem factor_completionProjection {k l : ℕ} (h : k ≤ l) (x : completion I hI) :
    _root_.LieIdeal.factor (hI h) (completionProjection I hI l x) =
      completionProjection I hI k x := by
  simpa only [completionProjection_apply, completionFiltration_transition,
    LieHom.coe_toLinearMap] using
    (completionFiltration I hI).transition_projection h x

variable {M : Type*} [LieRing M] [LieAlgebra R M]

/-- Lift a compatible family of Lie homomorphisms to the Lie completion. -/
def completionLift (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k)
    (hf : ∀ k l (h : k ≤ l), (_root_.LieIdeal.factor (hI h)).comp (f l) = f k) :
    M →ₗ⁅R⁆ completion I hI where
  __ := (completionFiltration I hI).lift (fun k => (f k).toLinearMap) (by
    intro k l h
    rw [completionFiltration_transition]
    exact congrArg LieHom.toLinearMap (hf k l h))
  map_lie' := by
    intro x y
    apply Mei.ModuleFiltration.completion_ext
    intro k
    simpa only [projection_bracket,
      Mei.ModuleFiltration.projection_lift, LinearMap.coe_mk, LinearMap.toFun_eq_coe,
      LieHom.coe_toLinearMap] using (f k).map_lie x y

/-- The lift has the prescribed finite-order components. -/
@[simp]
theorem completionProjection_lift (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k) (hf)
    (k : ℕ) (x : M) :
    completionProjection I hI k (completionLift I hI f hf x) = f k x := by
  rw [completionProjection_apply, completionLift]
  exact Mei.ModuleFiltration.projection_lift _ _ _ k x

/-- The compatible lift is uniquely determined by its projections. -/
theorem completionLift_unique (f : ∀ k, M →ₗ⁅R⁆ L ⧸ I k) (hf)
    (g : M →ₗ⁅R⁆ completion I hI)
    (hg : ∀ k, (completionProjection I hI k).comp g = f k) :
    g = completionLift I hI f hf := by
  apply LieHom.ext
  intro x
  apply Mei.ModuleFiltration.completion_ext
  intro k
  simpa only [LieHom.comp_apply, completionProjection_apply] using
    (LieHom.congr_fun (hg k) x).trans (completionProjection_lift I hI f hf k x).symm

/-- The canonical Lie homomorphism sends an element to its quotient classes. -/
def toCompletion : L →ₗ⁅R⁆ completion I hI :=
  completionLift I hI (fun k => (I k).mkQ) (by
    intro k l h
    apply LieHom.ext
    intro x
    simp [_root_.LieIdeal.mkQ_apply])

/-- The canonical map has the usual class in every quotient. -/
@[simp]
theorem completionProjection_toCompletion (k : ℕ) (x : L) :
    completionProjection I hI k (toCompletion I hI x) = (I k).mkQ x := by
  rw [toCompletion, completionProjection_lift]

end Mei.LieIdeal
