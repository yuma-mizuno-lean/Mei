/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cutoff
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Map
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Linear
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Completed evaluation over all encounter itineraries

For a fixed finite signed encounter alphabet, the actual cutoff decorated-ray
sums of a positive Lie action commute with coefficient truncation. A surviving
history has every segment degree in the smaller cutoff, so the larger inventory
contributes exactly the smaller ray fiber after zero decorations are discarded.
The compatible linear evaluation maps lift to a linear map into
`ShiftedCoefficients`, with each projection equal to the full finite weighted
evaluation at that order. This retains cancellations and scalar annihilation
at each finite stage and in the completion.

All encounters and geometric admission conditions are retained at every order.
The labels may become identities after truncation; their supports remain in the
fixed alphabet. This construction does not compare inventories obtained by
deleting inactive walls, or assert local constancy across endpoint discriminants.

We combine `map_cutoffDecoratedEvaluation` and
`cutoffDecoratedEvaluation_eq_of_supported` with
`ModuleFiltration.transition_truncatedBCHAction` and the inherited shifted
quotient gradings. The inverse-limit interpretation follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and Theorem 2.14 (arXiv:1503.06183v5).

The completed-label compatibility argument adapts the fixed-itinerary construction
`PositiveDegrees.completedBCHDecoratedRayEvaluation` in
`Mei.Geometry.ScatteringDiagram.BrokenLine.Truncation` to all encounter itineraries.
The completion is the `ModuleFiltration.lift` of the finite linear evaluations
`cutoffDecoratedEvaluationLinearMap`; its projections use the universal lift
formula, and `map_zero` gives the zero case.
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K I : Type*}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V) (Q : V)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G" => fun k : ℕ =>
  TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun (k : ℕ) (g : J → d.truncatedGroup ℒ k) (j : J) =>
  LinearEquiv.toLinearMap
    (ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p) d ℒ k (g j))

/-- Truncation commutes with the complete finite ray sum over every encounter
word. The smaller cutoff omits precisely the histories whose coefficients vanish;
the surviving rays keep every encounter and their geometric realization. -/
theorem transition_cutoffDecoratedEvaluation_shiftedBCHAction
    {k l : ℕ} (h : k ≤ l) (g : J → d.truncatedGroup ℒ l) (a : G l 0) :
    (F).transition h
        (cutoffDecoratedEvaluation d (G l) (T l g) a v f c ε P W S C l Q) =
      cutoffDecoratedEvaluation d (G k)
        (T k (fun j => (d.truncationMap ℒ h).bchGroupMap (g j)))
        ⟨(F).transition h a, d.transition_mem_shiftedQuotientGrading ℳ p h a.property⟩
        v f c ε P W S C k Q := by
  rw [map_cutoffDecoratedEvaluation (W := W) d (G l) (G k) ((F).transition h)
    (fun _ _ hx => d.transition_mem_shiftedQuotientGrading ℳ p h hx)
    (T l g) (T k (fun j => (d.truncationMap ℒ h).bchGroupMap (g j)))
    (fun j => LinearMap.ext fun x => (F).transition_truncatedBCHAction d ℒ h (g j) x)]
  exact cutoffDecoratedEvaluation_eq_of_supported d (G k) _ _ v f c ε P W S C h
    (fun _ _ hx hne => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p hx hne) Q

-- Restricting the quotient map changes only the homogeneous membership proof;
-- its underlying function is the quotient class of the original input.
local notation "input" => fun k : ℕ =>
  LinearMap.codRestrict (G k 0)
    (LinearMap.comp (Submodule.mkQ (ModuleFiltration.submodule F (k + 1)))
      (Submodule.subtype (shiftedGrading ℳ d.monoid p 0)))
    (fun a => Iff.mpr (mem_shiftedQuotientGrading_iff d ℳ p)
      (Exists.intro a (And.intro (Subtype.property a) rfl)))

/-- The full finite evaluations of completed labels form a compatible quotient
family, for an original relative-degree-zero incoming coefficient. -/
theorem transition_cutoffDecoratedEvaluation_completedBCHAction
    {k l : ℕ} (h : k ≤ l) (g : J → d.completedBCHGroup ℒ)
    (a : shiftedGrading ℳ d.monoid p 0) :
    (F).transition h
        (cutoffDecoratedEvaluation d (G l) (T l (fun j => CompletedGroup.projection l (g j)))
          (input l a) v f c ε P W S C l Q) =
      cutoffDecoratedEvaluation d (G k) (T k (fun j => CompletedGroup.projection k (g j)))
        (input k a) v f c ε P W S C k Q := by
  have hg (j : J) :
      (d.truncationMap ℒ h).bchGroupMap (CompletedGroup.projection l (g j)) =
        CompletedGroup.projection k (g j) :=
    CompletedGroup.map_projection k l h (g j)
  have ha : (⟨(F).transition h (input l a),
      d.transition_mem_shiftedQuotientGrading ℳ p h (input l a).property⟩ : G k 0) =
      input k a := by
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.subtype_apply, ModuleFiltration.transition_mk]
  simpa only [hg, ha] using
    d.transition_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℳ p v f c ε P W S C Q h
      (fun j => CompletedGroup.projection l (g j)) (input l a)

/-- The completed weighted evaluation of all finite encounter itineraries in
a fixed finite alphabet, linear in the original relative-degree-zero input.
Its order-`k` value is the actual full cutoff ray sum. -/
def completedBCHCutoffEvaluation (g : J → d.completedBCHGroup ℒ) :
    shiftedGrading ℳ d.monoid p 0 →ₗ[R] d.ShiftedCoefficients ℳ p :=
  (F).lift
    (fun k => (cutoffDecoratedEvaluationLinearMap d (G k)
      (T k (fun j => CompletedGroup.projection k (g j)))
      v f c ε P W S C k Q).comp (input k))
    (fun k l h => LinearMap.ext fun a => by
      simpa only [LinearMap.comp_apply, cutoffDecoratedEvaluationLinearMap_apply] using
        d.transition_cutoffDecoratedEvaluation_completedBCHAction ℒ ℳ p
          v f c ε P W S C Q h g a)

/-- Each projection of the completed evaluation is the whole finite weighted
ray sum at that cutoff, without fixing an encounter word in advance. -/
@[simp]
theorem projection_completedBCHCutoffEvaluation
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0) (k : ℕ) :
    (F).projection k (d.completedBCHCutoffEvaluation ℒ ℳ p v f c ε P W S C Q g a) =
      cutoffDecoratedEvaluation d (G k) (T k (fun j => CompletedGroup.projection k (g j)))
        (input k a) v f c ε P W S C k Q := by
  rw [completedBCHCutoffEvaluation, ModuleFiltration.projection_lift,
    LinearMap.comp_apply, cutoffDecoratedEvaluationLinearMap_apply]

end Mei.PositiveDegrees
