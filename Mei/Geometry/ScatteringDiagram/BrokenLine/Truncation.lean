/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.CoefficientMap
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient

/-!
# Truncation of decorated rays with BCH propagation

For a fixed signed encounter itinerary, coefficient truncation commutes with
weighted evaluation of the actual decorated rays of a positive Lie action.
The propagation maps are the finite BCH actions on the existing shifted
quotients, with their inherited relative gradings. Truncation may kill whole
decorations; these rays disappear from the lower-order evaluation. No endpoint
genericity or injectivity of truncation is required.

Compatible completed labels and an original homogeneous input therefore give
a completed coefficient whose projections are these finite ray sums. The
geometry, including the recorded encounters and incoming source, is fixed
throughout this comparison. Removing encounters at walls which become inactive,
or summing over all encounter itineraries, requires a further comparison.

This applies `map_decoratedRayEvaluation` to `shiftedQuotientGrading` and
`ModuleFiltration.transition_truncatedBCHAction`. Whole-component propagation
and its inverse-limit interpretation follow Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and Theorem 2.14
(arXiv:1503.06183v5).
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
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (v : Γ → V) (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (ε : Fin n → SignType) (P : Fin n → Set V) (W : J → Set V)
  (S : K → Set V) (C : Set V) (Q : V)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G" => fun k : ℕ =>
  TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun (k : ℕ) (g : Fin n → d.truncatedGroup ℒ k) (j : Fin n) =>
  LinearEquiv.toLinearMap
    (ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p) d ℒ k (g j))

/-- Truncation of the actual weighted ray sum is the ray sum for the truncated
BCH labels and input. Geometry and relative degrees are unchanged, while zero
output decorations are discarded. The input can have any retained relative degree. -/
theorem transition_decoratedRayEvaluation_shiftedBCHAction
    {k l : ℕ} (h : k ≤ l) (g : Fin n → d.truncatedGroup ℒ l)
    (r : Γ) (a : G l r) :
    (F).transition h
        (decoratedRayEvaluation (G l) (T l g) r a v f c ε P W S C Q) =
      decoratedRayEvaluation (G k)
        (T k (fun j => (d.truncationMap ℒ h).bchGroupMap (g j))) r
        ⟨(F).transition h a, d.transition_mem_shiftedQuotientGrading ℳ p h a.property⟩
        v f c ε P W S C Q := by
  exact map_decoratedRayEvaluation (G l) (G k) ((F).transition h) id
    (fun _ _ hx => d.transition_mem_shiftedQuotientGrading ℳ p h hx)
    (T l g) (T k (fun j => (d.truncationMap ℒ h).bchGroupMap (g j)))
    (fun j => LinearMap.ext fun x => (F).transition_truncatedBCHAction d ℒ h (g j) x)
    r a v v (fun _ => rfl) f c ε P W S C Q

local notation "input" => fun (k : ℕ) {r : Γ} (a : shiftedGrading ℳ d.monoid p r) =>
  (Subtype.mk (Submodule.Quotient.mk (a : shiftedSubmodule ℳ d.monoid p))
    (Iff.mpr (mem_shiftedQuotientGrading_iff d ℳ p)
      (Exists.intro a (And.intro (Subtype.property a) rfl))) : G k r)

/-- Finite decorated-ray sums for projections of completed labels form a
compatible quotient family. The homogeneous input is taken in the original
shifted module, rather than chosen independently at each cutoff. -/
theorem transition_decoratedRayEvaluation_completedBCHAction
    {k l : ℕ} (h : k ≤ l) (g : Fin n → d.completedBCHGroup ℒ)
    (r : Γ) (a : shiftedGrading ℳ d.monoid p r) :
    (F).transition h
        (decoratedRayEvaluation (G l) (T l (fun j => CompletedGroup.projection l (g j)))
          r (input l a) v f c ε P W S C Q) =
      decoratedRayEvaluation (G k) (T k (fun j => CompletedGroup.projection k (g j)))
        r (input k a) v f c ε P W S C Q := by
  have hg (j : Fin n) :
      (d.truncationMap ℒ h).bchGroupMap (CompletedGroup.projection l (g j)) =
        CompletedGroup.projection k (g j) :=
    CompletedGroup.map_projection k l h (g j)
  simpa only [hg, ModuleFiltration.transition_mk] using
    d.transition_decoratedRayEvaluation_shiftedBCHAction ℒ ℳ p v f c ε P W S C Q h
      (fun j => CompletedGroup.projection l (g j)) r (input l a)

/-- The completed weighted evaluation for one fixed signed itinerary and
homogeneous input. Each quotient is the finite sum of whole final decorations
of the actual admissible rays at that order. -/
def completedBCHDecoratedRayEvaluation (g : Fin n → d.completedBCHGroup ℒ)
    (r : Γ) (a : shiftedGrading ℳ d.monoid p r) : d.ShiftedCoefficients ℳ p :=
  ⟨fun k => decoratedRayEvaluation (G k.unop)
      (T k.unop (fun j => CompletedGroup.projection k.unop (g j)))
      r (input k.unop a) v f c ε P W S C Q,
    ((F).mem_completionSubmodule_iff _).mpr fun _ _ h =>
      d.transition_decoratedRayEvaluation_completedBCHAction ℒ ℳ p v f c ε P W S C Q h g r a⟩

/-- The completed evaluation retains exactly the actual finite ray sum in
each quotient; it does not require one global finite inventory of histories. -/
@[simp]
theorem projection_completedBCHDecoratedRayEvaluation
    (g : Fin n → d.completedBCHGroup ℒ) (r : Γ)
    (a : shiftedGrading ℳ d.monoid p r) (k : ℕ) :
    (F).projection k (d.completedBCHDecoratedRayEvaluation ℒ ℳ p v f c ε P W S C Q g r a) =
      decoratedRayEvaluation (G k) (T k (fun j => CompletedGroup.projection k (g j)))
        r (input k a) v f c ε P W S C Q := by
  rw [completedBCHDecoratedRayEvaluation, ModuleFiltration.projection_mk]

/-- An input above a cutoff contributes no ray sum in that quotient, even
when its decoration and its rays survive at higher orders. -/
theorem projection_completedBCHDecoratedRayEvaluation_eq_zero_of_lt
    (g : Fin n → d.completedBCHGroup ℒ) (r : Γ)
    (a : shiftedGrading ℳ d.monoid p r) {k : ℕ} (hk : (k : ℤ) < d.degree r) :
    (F).projection k (d.completedBCHDecoratedRayEvaluation ℒ ℳ p v f c ε P W S C Q g r a) =
      0 := by
  rw [projection_completedBCHDecoratedRayEvaluation]
  have hz : input k a = (0 : G k r) := by
    apply Subtype.ext
    exact (Submodule.mem_bot R).mp (by
      simpa only [shiftedQuotientGrading_piece, d.map_shiftedGrading_eq_bot ℳ p hk]
        using (input k a).property)
  rw [hz, decoratedRayEvaluation_zero]

/-- A vanished incoming coefficient has zero completed weighted evaluation. -/
@[simp]
theorem completedBCHDecoratedRayEvaluation_zero
    (g : Fin n → d.completedBCHGroup ℒ) (r : Γ) :
    d.completedBCHDecoratedRayEvaluation ℒ ℳ p v f c ε P W S C Q g r 0 = 0 := by
  apply (F).completion_ext
  intro k
  rw [projection_completedBCHDecoratedRayEvaluation, map_zero]
  have hz : input k (0 : shiftedGrading ℳ d.monoid p r) = (0 : G k r) := by
    apply Subtype.ext
    exact Submodule.Quotient.mk_zero _
  rw [hz, decoratedRayEvaluation_zero]

end Mei.PositiveDegrees
