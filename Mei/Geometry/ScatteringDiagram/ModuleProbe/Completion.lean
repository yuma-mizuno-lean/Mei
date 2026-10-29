/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Conjugation

/-!
# Completed coefficient labels in module probes

The additive completion of a shifted coefficient module embeds in the completed
probe group. Relative order `k` is read at probe order `k + 1`, because the
coefficient summand has charge one. Logarithmic projection recovers every finite
coefficient, so the embedding remains injective without separatedness of the
original module. Conjugation by a completed charge-zero label is the completed
BCH action on coefficients.

We assemble `ModuleProbe.moduleBCHInclusion` using `CompletedGroup.lift` and
pass `ModuleProbe.base_conj_moduleBCHInclusion` through the finite projections.
The probe construction and its transport interpretation follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

section Inclusion

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] [Algebra ℚ R]

private def moduleBCHComponent (k : ℕ) :
    Multiplicative (d.shiftedFiltration ℳ p).completion →*
      BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) k) :=
  (((positiveDegrees d p).truncationMap (grading d ℳ p ℒ)
      (Nat.le_succ k)).bchGroupMap.comp (moduleBCHInclusion d ℳ p ℒ k)).comp
    ((d.shiftedFiltration ℳ p).projection k).toAddMonoidHom.toMultiplicative

private theorem moduleBCHComponent_apply (k : ℕ)
    (a : Multiplicative (d.shiftedFiltration ℳ p).completion) :
    moduleBCHComponent d ℳ p ℒ k a =
      BCHGroup.exp ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ)
        (Nat.le_succ k) (moduleQuotientInclusion d ℳ p ℒ k
          ((d.shiftedFiltration ℳ p).projection k a.toAdd))) := by
  simp [moduleBCHComponent, AddMonoidHom.toMultiplicative]

private theorem moduleBCHComponent_compatible (k l : ℕ) (h : k ≤ l) :
    (((positiveDegrees d p).groupTower (grading d ℳ p ℒ)).map
      (CategoryTheory.homOfLE h).op).hom.comp (moduleBCHComponent d ℳ p ℒ l) =
        moduleBCHComponent d ℳ p ℒ k := by
  apply MonoidHom.ext
  intro a
  -- The tower's categorical objects are the concrete finite BCH quotients.
  change ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) h).bchGroupMap
    (moduleBCHComponent d ℳ p ℒ l a) = moduleBCHComponent d ℳ p ℒ k a
  simp only [moduleBCHComponent_apply, LieHom.bchGroupMap_exp]
  congr 1
  rw [← LieHom.comp_apply, PositiveDegrees.truncationMap_comp,
    ← PositiveDegrees.truncationMap_comp (positiveDegrees d p) (grading d ℳ p ℒ)
      (Nat.le_succ k) (Nat.add_le_add_right h 1), LieHom.comp_apply,
    truncationMap_moduleQuotientInclusion d ℳ p ℒ h,
    ModuleFiltration.transition_projection]

/-- Exponentiation includes completed shifted coefficients as charge-one probe labels. -/
def completedModuleBCHInclusion :
    Multiplicative (d.shiftedFiltration ℳ p).completion →*
      (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ) :=
  CompletedGroup.lift (moduleBCHComponent d ℳ p ℒ)
    (moduleBCHComponent_compatible d ℳ p ℒ)

/-- At extended order `k + 1`, the completed label is the finite inclusion of the
relative order-`k` coefficient. -/
@[simp]
theorem projection_completedModuleBCHInclusion (k : ℕ)
    (a : Multiplicative (d.shiftedFiltration ℳ p).completion) :
    CompletedGroup.projection (k + 1) (completedModuleBCHInclusion d ℳ p ℒ a) =
      moduleBCHInclusion d ℳ p ℒ k
        (Multiplicative.ofAdd ((d.shiftedFiltration ℳ p).projection k a.toAdd)) := by
  have hp := CompletedGroup.projection_lift
    (F := (positiveDegrees d p).groupTower (grading d ℳ p ℒ))
    (moduleBCHComponent d ℳ p ℒ)
    (moduleBCHComponent_compatible d ℳ p ℒ) (k + 1) a
  have hc : moduleBCHComponent d ℳ p ℒ (k + 1) a =
      moduleBCHInclusion d ℳ p ℒ k
        (Multiplicative.ofAdd ((d.shiftedFiltration ℳ p).projection k a.toAdd)) := by
    rw [moduleBCHComponent_apply, moduleBCHInclusion_apply, toAdd_ofAdd]
    exact congrArg BCHGroup.exp
      ((truncationMap_moduleQuotientInclusion d ℳ p ℒ (Nat.le_succ k) _).trans
        (congrArg (moduleQuotientInclusion d ℳ p ℒ k)
          ((d.shiftedFiltration ℳ p).transition_projection (Nat.le_succ k) a.toAdd)))
  exact hp.trans hc

/-- Distinct completed coefficients give distinct completed probe labels. -/
theorem completedModuleBCHInclusion_injective :
    Function.Injective (completedModuleBCHInclusion d ℳ p ℒ) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply ModuleFiltration.completion_ext
  intro k
  have h := congrArg (CompletedGroup.projection (k + 1)) hab
  rw [projection_completedModuleBCHInclusion, projection_completedModuleBCHInclusion] at h
  exact Multiplicative.ofAdd.injective (moduleBCHInclusion_injective d ℳ p ℒ k h)

/-- The completed inclusion extends exponentiation of original shifted coefficients. -/
@[simp]
theorem completedModuleBCHInclusion_of (a : shiftedSubmodule ℳ d.monoid p) :
    completedModuleBCHInclusion d ℳ p ℒ
        (Multiplicative.ofAdd ((d.shiftedFiltration ℳ p).of a)) =
      (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a)) := by
  apply CompletedGroup.ext
  intro k
  cases k with
  | zero =>
    -- The categorical tower object hides the concrete trivial order-zero BCH group.
    exact @Subsingleton.elim
      (BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) 0)) _ _ _
  | succ k =>
    simp only [projection_completedModuleBCHInclusion, ModuleFiltration.projection_of,
      moduleBCHInclusion_apply, toAdd_ofAdd, moduleQuotientInclusion_mk,
      PositiveDegrees.projection_expToCompletion]
    rfl

end Inclusion

universe u

variable {R Γ : Type*} {M L : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Conjugation of a completed coefficient label by a completed charge-zero label
is exactly the integrated BCH coefficient action. -/
theorem base_conj_completedModuleBCHInclusion (g : d.completedBCHGroup ℒ)
    (a : Multiplicative (d.shiftedFiltration ℳ p).completion) :
    (baseGradedLieHom d ℳ p ℒ).completedMap g * completedModuleBCHInclusion d ℳ p ℒ a *
        ((baseGradedLieHom d ℳ p ℒ).completedMap g)⁻¹ =
      completedModuleBCHInclusion d ℳ p ℒ (Multiplicative.ofAdd
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g a.toAdd)) := by
  apply CompletedGroup.ext
  intro k
  cases k with
  | zero =>
    -- The categorical tower object hides the concrete trivial order-zero BCH group.
    exact @Subsingleton.elim
      (BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) 0)) _ _ _
  | succ k =>
    have hb : CompletedGroup.projection (k + 1)
        ((baseGradedLieHom d ℳ p ℒ).completedMap g) =
        ((baseGradedLieHom d ℳ p ℒ).truncatedMap (a := k + 1) (k + 1)
          (by simp)).bchGroupMap (CompletedGroup.projection (k + 1) g) :=
      GradedLieHom.projection_completedMap_of_le (baseGradedLieHom d ℳ p ℒ)
        (k + 1) (by simp) g
    have hg := CompletedGroup.map_projection k (k + 1) (Nat.le_succ k) g
    -- Express the categorical tower transition as the concrete BCH quotient map.
    change (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
      (CompletedGroup.projection (k + 1) g) = CompletedGroup.projection k g at hg
    have hc := base_conj_moduleBCHInclusion d ℳ p ℒ k
      (CompletedGroup.projection (k + 1) g)
      (Multiplicative.ofAdd ((d.shiftedFiltration ℳ p).projection k a.toAdd))
    rw [hg] at hc
    rw [map_mul, map_mul, map_inv, hb, projection_completedModuleBCHInclusion,
      projection_completedModuleBCHInclusion]
    rw [toAdd_ofAdd,
      (d.shiftedLieFiltration ℒ ℳ p).projection_completedBCHAction d ℒ g a.toAdd k]
    exact hc

end Mei.ModuleProbe
