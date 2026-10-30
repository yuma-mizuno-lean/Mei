/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Exhaustion of finite BCH rays by cutoff types

For signed BCH propagation on a finite shifted coefficient quotient, every
contributing decorated ray automatically satisfies the positive cutoff and
monotone degree conditions. Thus the unrestricted family over all finite
encounter words is exactly the existing cutoff family. In particular its
endpoint fibers and its realized degree itineraries across all endpoints are
finite, without assuming a bound on the number of encounters.

The equivalence keeps the full geometric realization, incoming source, encounter
parameters and whole decorations. Labels may include inverses and combined
simultaneous crossings. Degree shifts with zero spatial projection remain
recorded. Normal-velocity and crossing-sign conditions are those of the existing
`DecoratedAdmissibleRay`; no new conditions on coefficient histories are imposed.

The algebraic input is
`PositiveDegrees.homogeneousHistory_shiftedBCHAction_sub_mem_monoid_of_le`;
the geometric input is `CutoffDecoratedRay.degreeItinerary_mem`. Together they
implement the finite-type argument of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Proposition 2.13
(arXiv:1503.06183v5), on the existing backward-ray parameterization.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ) (k : ℕ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

variable (g : J → d.truncatedGroup ℒ k) (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)

/-- The unrestricted family over all finite encounter words is exactly the
cutoff family for actual BCH propagation. Both cutoff constraints are derived. -/
def shiftedBCHRayCutoffEquiv (Q : V) :
    (Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) ≃
      CutoffDecoratedRay d (d.shiftedQuotientGrading ℳ p k).piece
        (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap)
        a v f c ε P W S C k Q where
  toFun β := {
    itinerary := β.1
    realization := β.2
    degree_mem := fun j => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p
      (β.2.decoration_mem j) (β.2.decoration_ne_zero j.castSucc)
    degree_sub_mem := by
      intro i j hij
      have hne := ((mem_decoratedHistorySupport _ _ _ _ _ _ _ _).mp β.2.1.property).1
      simpa only [Fin.snoc_castSucc] using
        d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid_of_le ℒ ℳ p k
          (fun j => g (β.1.get j)) β.2.1.val 0 a hne i.castSucc j.castSucc hij }
  invFun β := ⟨β.itinerary, β.realization⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exhaustion retains the exact encounter word. -/
@[simp]
theorem shiftedBCHRayCutoffEquiv_itinerary (Q : V)
    (β : Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q β).itinerary = β.1 :=
  (rfl)

/-- Exhaustion retains the entire decorated realization, including its incoming
tail, crossing times, paths and all intermediate decorations. -/
@[simp]
theorem shiftedBCHRayCutoffEquiv_realization (Q : V)
    (β : Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    HEq (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q β).realization β.2 :=
  (HEq.rfl)

/-- The inverse forgets only the proofs of the two derived degree constraints. -/
@[simp]
theorem shiftedBCHRayCutoffEquiv_symm_apply (Q : V)
    (β : CutoffDecoratedRay d (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap)
      a v f c ε P W S C k Q) :
    (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q).symm β =
      ⟨β.itinerary, β.realization⟩ := (rfl)

/-- Exhaustion preserves the whole final coefficient. -/
@[simp↓]
theorem shiftedBCHRayCutoffEquiv_decoration (Q : V)
    (β : Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q β).decoration =
      β.2.decoration 0 := by
  rw [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero]
  rfl

/-- At a fixed endpoint there are finitely many actual BCH-decorated rays over
all encounter words. Neither a word-length bound nor degree bounds are assumed. -/
instance finite_shiftedBCHDecoratedRays [Finite J] (Q : V) :
    Finite (Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :=
  Finite.of_equiv _ (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q).symm

/-- Every actual BCH-decorated ray obeys a uniform bound on its total number of
encounters, including encounters that preserve degree. -/
theorem decoratedAdmissibleRay_shiftedBCH_length_le [Finite J] {l : List J} {Q : V}
    (β : DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q) :
    l.length ≤ Nat.card (d.cutoff k) * Nat.card J :=
  (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q ⟨l, β⟩).length_le

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
  have hm := (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q
    ⟨l, β⟩).degreeItinerary_mem
  rw [CutoffDecoratedRay.degreeItinerary_eq] at hm
  exact hm

/-- The existing cutoff evaluation sums exactly all actual BCH-decorated rays,
with no a priori restriction on their encounter words or degree histories. -/
theorem cutoffDecoratedEvaluation_shiftedBCH_eq_sum [Finite J] (Q : V) :
    cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap)
      a v f c ε P W S C k Q =
      let := Fintype.ofFinite
        (Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
          (fun j => f (l.get j)) (fun j => c (l.get j))
          (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q)
      ∑ β : (Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
          (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
          (fun j => f (l.get j)) (fun j => c (l.get j))
          (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q),
        β.2.decoration 0 := by
  let := Fintype.ofFinite
    (Σ l : List J, DecoratedAdmissibleRay (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g (l.get j))).toLinearMap) 0 a v
      (fun j => f (l.get j)) (fun j => c (l.get j))
      (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q)
  let := Fintype.ofFinite (CutoffDecoratedRay d (d.shiftedQuotientGrading ℳ p k).piece
    (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) a v f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def]
  exact (Fintype.sum_equiv
    (d.shiftedBCHRayCutoffEquiv ℒ ℳ p k g a v f c ε P W S C Q) _ _
    (fun β =>
      (d.shiftedBCHRayCutoffEquiv_decoration ℒ ℳ p k g a v f c ε P W S C Q β).symm)).symm

end Mei.PositiveDegrees
