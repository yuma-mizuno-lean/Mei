/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cutoff
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Map
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Completed evaluation over all encounter itineraries

For a fixed finite signed encounter alphabet, the actual cutoff decorated-ray
sums of a positive Lie action commute with coefficient truncation. A surviving
history has every segment degree in the smaller cutoff, so the larger inventory
contributes exactly the smaller ray fiber after zero decorations are discarded.
The compatible sums define a coefficient in `ShiftedCoefficients`, with each
projection equal to the full finite weighted evaluation at that order.

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

The input construction, completed-label compatibility, completion definition,
projection theorem and zero proof adapt the fixed-itinerary construction
`PositiveDegrees.completedBCHDecoratedRayEvaluation` in
`Mei.Geometry.ScatteringDiagram.BrokenLine.Truncation` to all encounter itineraries.
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K : Type*}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

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
  rw [map_cutoffDecoratedEvaluation d (G l) (G k) ((F).transition h)
    (fun _ _ hx => d.transition_mem_shiftedQuotientGrading ℳ p h hx)
    (T l g) (T k (fun j => (d.truncationMap ℒ h).bchGroupMap (g j)))
    (fun j => LinearMap.ext fun x => (F).transition_truncatedBCHAction d ℒ h (g j) x)]
  exact cutoffDecoratedEvaluation_eq_of_supported d (G k) _ _ v f c ε P W S C h
    (fun _ _ hx hne => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p hx hne) Q

local notation "input" => fun (k : ℕ) (a : shiftedGrading ℳ d.monoid p 0) =>
  (Subtype.mk (Submodule.Quotient.mk (a : shiftedSubmodule ℳ d.monoid p))
    (Iff.mpr (mem_shiftedQuotientGrading_iff d ℳ p)
      (Exists.intro a (And.intro (Subtype.property a) rfl))) : G k 0)

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
  simpa only [hg, ModuleFiltration.transition_mk] using
    d.transition_cutoffDecoratedEvaluation_shiftedBCHAction ℒ ℳ p v f c ε P W S C Q h
      (fun j => CompletedGroup.projection l (g j)) (input l a)

/-- The completed weighted evaluation of all finite encounter itineraries in
a fixed finite alphabet. Its order-`k` value is the actual full cutoff ray sum. -/
def completedBCHCutoffEvaluation (g : J → d.completedBCHGroup ℒ)
    (a : shiftedGrading ℳ d.monoid p 0) : d.ShiftedCoefficients ℳ p :=
  ⟨fun k => cutoffDecoratedEvaluation d (G k.unop)
      (T k.unop (fun j => CompletedGroup.projection k.unop (g j)))
      (input k.unop a) v f c ε P W S C k.unop Q,
    ((F).mem_completionSubmodule_iff _).mpr fun _ _ h =>
      d.transition_cutoffDecoratedEvaluation_completedBCHAction ℒ ℳ p v f c ε P W S C Q h g a⟩

/-- Each projection of the completed evaluation is the whole finite weighted
ray sum at that cutoff, without fixing an encounter word in advance. -/
@[simp]
theorem projection_completedBCHCutoffEvaluation
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0) (k : ℕ) :
    (F).projection k (d.completedBCHCutoffEvaluation ℒ ℳ p v f c ε P W S C Q g a) =
      cutoffDecoratedEvaluation d (G k) (T k (fun j => CompletedGroup.projection k (g j)))
        (input k a) v f c ε P W S C k Q := by
  rw [completedBCHCutoffEvaluation, ModuleFiltration.projection_mk]

/-- Zero incoming coefficient has zero completed evaluation, including when
nonzero coefficients can be killed at individual cutoffs. -/
@[simp]
theorem completedBCHCutoffEvaluation_zero (g : J → d.completedBCHGroup ℒ) :
    d.completedBCHCutoffEvaluation ℒ ℳ p v f c ε P W S C Q g 0 = 0 := by
  apply (F).completion_ext
  intro k
  rw [projection_completedBCHCutoffEvaluation, map_zero]
  have hz : input k (0 : shiftedGrading ℳ d.monoid p 0) = (0 : G k 0) := by
    apply Subtype.ext
    exact Submodule.Quotient.mk_zero _
  rw [hz, cutoffDecoratedEvaluation_zero]

end Mei.PositiveDegrees
