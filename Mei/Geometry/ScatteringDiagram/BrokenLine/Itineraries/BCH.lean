/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Path
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Exhaustion of finite BCH rays by cutoff types

For signed BCH propagation on a finite shifted coefficient quotient, every
contributing decorated ray automatically satisfies the positive cutoff and
monotone degree conditions. Thus the unrestricted family over all finite
encounter words is exactly the existing cutoff family, for any encounter
alphabet `J`, and the cutoff evaluation is the common weighted evaluation of
decorated rays along all paths of the one-object quiver on `J`. When `J` is
finite, its endpoint fibers and its realized degree itineraries across all
endpoints are finite, without assuming a bound on the number of encounters.

The comparison keeps the full geometric realization, incoming source, encounter
parameters and whole decorations. Labels may include inverses and combined
simultaneous crossings. Degree shifts with zero spatial projection remain
recorded. Normal-velocity and crossing-sign conditions are those of the existing
`DecoratedAdmissibleRay`; no new conditions on coefficient histories are imposed.

The algebraic input is `mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero` and
`sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero`, fed to
`cutoffDecoratedRayWordEquiv`; the geometric input is
`CutoffDecoratedRay.degreeItinerary_mem`. Together they implement the finite-type
argument of Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Proposition 2.13 (arXiv:1503.06183v5), on the existing backward-ray
parameterization.
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K I : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ) (k : ℕ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

variable (g : J → d.truncatedGroup ℒ k) (a : (d.shiftedQuotientGrading ℳ p k).piece 0)
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

/-- Actual BCH-decorated rays at an endpoint, over all finite encounter words,
without imposing cutoff constraints on their degree histories. -/
abbrev ShiftedBCHDecoratedRays (Q : V) :=
    Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q

/-- Every actual BCH-decorated ray of every word satisfies both cutoff conditions. -/
theorem shiftedBCH_cutoff_conditions {Q : V} (l : List J)
    (r : DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    (∀ j, r.1.val j ∈ d.cutoff k) ∧ ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid :=
  DecoratedAdmissibleRay.cutoff_conditions_of_sub_mem d (d.shiftedQuotientGrading ℳ p k).piece
    (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap) a v f c ε P W S C
    (fun hx hne => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p hx hne)
    (fun e _ _ _ hx hq => d.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero ℒ ℳ p k (g e)
      hx hq) l r

/-- At a fixed endpoint there are finitely many actual BCH-decorated rays over
all encounter words. Neither a word-length bound nor degree bounds are assumed. -/
instance finite_shiftedBCHDecoratedRays [Finite J] (Q : V) :
    Finite (d.ShiftedBCHDecoratedRays ℒ ℳ p k g a v f c ε P W S C Q) :=
  Finite.of_equiv _ (cutoffDecoratedRayWordEquiv d _
    (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap) a v f c ε P W S C (Q := Q)
    (d.shiftedBCH_cutoff_conditions ℒ ℳ p k g a v f c ε P W S C))

/-- Every actual BCH-decorated ray obeys a uniform bound on its total number of
encounters, including encounters that preserve degree. -/
theorem decoratedAdmissibleRay_shiftedBCH_length_le [Finite J] {l : List J} {Q : V}
    (β : DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    l.length ≤ Nat.card (d.cutoff k) * Nat.card J := by
  simpa using ((cutoffDecoratedRayWordEquiv d _
    (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap) a v f c ε P W S C
    (d.shiftedBCH_cutoff_conditions ℒ ℳ p k g a v f c ε P W S C)).symm ⟨l, β⟩).length_le

/-- Across all endpoints, only finitely many degree-labelled encounter words
are realized by actual BCH propagation. Equal spatial directions do not identify
different coefficient degrees or omit unchanged-degree encounters. -/
theorem finite_shiftedBCH_realizedDegreeItineraries [Finite J] :
    Set.Finite {w : List (Γ × J) | ∃ (l : List J) (Q : V)
      (β : DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
        (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
        (fun j => f (l.get j)) (fun j => c (l.get j))
        (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q),
      w = List.ofFn fun j => (β.1.val j, l.get j)} := by
  apply (finite_realizedDegreeItineraries d f c v k).subset
  rintro w ⟨l, Q, β, rfl⟩
  simpa using ((cutoffDecoratedRayWordEquiv d _
    (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap) a v f c ε P W S C
    (d.shiftedBCH_cutoff_conditions ℒ ℳ p k g a v f c ε P W S C)).symm
    ⟨l, β⟩).degreeItinerary_mem

/-- The cutoff evaluation of BCH propagation is the common weighted evaluation of
decorated rays along paths of the one-object quiver on the encounter alphabet, over any
finite inventory containing every path that carries a ray at the endpoint. -/
theorem cutoffDecoratedEvaluation_shiftedBCH_eq_pathDecoratedEvaluation [Finite J] {Q : V}
    (s : Finset (Path (SingleObj.star J) (SingleObj.star J)))
    (hs : ∀ q, PathDecoratedRay (Q := SingleObj J) (M := fun _ => (F).quotient k)
      (ι := fun _ => Γ) (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap)
      (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a (fun _ => v) (fun e => f e)
      (fun e => ε e) (fun e => c e) (fun e => P e) W S C q Q → q ∈ s) :
    cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) a v f c ε P W S C k Q =
      pathDecoratedEvaluation (Q := SingleObj J) (M := fun _ => (F).quotient k)
        (ι := fun _ => Γ) (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap)
        (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a s (fun _ => v) (fun e => f e)
        (fun e => ε e) (fun e => c e) (fun e => P e) W S C Q :=
  cutoffDecoratedEvaluation_eq_pathDecoratedEvaluation d _ _ a v f c ε P W S C
    (d.shiftedBCH_cutoff_conditions ℒ ℳ p k g a v f c ε P W S C) s hs

end Mei.PositiveDegrees
