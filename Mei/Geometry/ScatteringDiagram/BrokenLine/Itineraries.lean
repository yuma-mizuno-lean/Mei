/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Finiteness
public import Mathlib.Data.Set.Finite.List

/-!
# Decorated rays over all finite encounter itineraries

At a fixed positive-degree cutoff, the full family of transverse decorated rays
has finite endpoint fibers. No encounter bound is assumed: decreasing relative
degrees and positive encounter times imply the bound from
`Convex.realizedDegreeItineraries`. Whole decorations, identity encounters and
nonzero degree shifts with unchanged spatial direction are retained. For a
nonstationary incoming direction, these rays are proper on closed half-lines.

The encounter alphabet can include crossing signs and simultaneous wall events.
Its propagation maps and signs are fixed before choosing an itinerary. The grading
is by relative degree, so the incoming homogeneous piece has index zero; spatial
directions may include a fixed initial exponent.

This joins `DecoratedAdmissibleRay` to the finite geometric itinerary inventory.
The backward parameterization follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2), and the finite-type argument
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)

/-- A cutoff decorated ray, with an arbitrary finite encounter itinerary.
All selected relative degrees lie in the cutoff and decrease in the positive
monoid when read backwards. There is no assumed bound on itinerary length. -/
structure CutoffDecoratedRay (k : ℕ) (Q : V) where
  /-- Every encounter is recorded, in backward order. -/
  itinerary : List J
  /-- The actual admissible ray with its whole homogeneous decorations. -/
  realization : DecoratedAdmissibleRay ℳ (fun j => T (itinerary.get j)) 0 a v
    (fun j => f (itinerary.get j)) (fun j => c (itinerary.get j))
    (fun j => ε (itinerary.get j)) (fun j => P (itinerary.get j)) W S C Q
  /-- Every selected relative degree survives the cutoff. -/
  degree_mem : ∀ j, realization.1.val j ∈ d.cutoff k
  /-- Forward component shifts belong to the positive monoid. -/
  degree_sub_mem : ∀ i j, i ≤ j → realization.1.val i - realization.1.val j ∈ d.monoid

namespace CutoffDecoratedRay

variable {d ℳ T a v f c ε P W S C} {k : ℕ} {Q : V}

/-- The final whole homogeneous decoration. -/
def decoration (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) : M :=
  r.realization.decoration 0

/-- The final decoration is the last propagated whole component. -/
@[simp]
theorem decoration_eq (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.decoration = homogeneousHistory ℳ (fun j => T (r.itinerary.get j))
      r.realization.1.val a := by
  rw [decoration, DecoratedAdmissibleRay.decoration_zero]

/-- The final decoration is nonzero. -/
theorem decoration_ne_zero (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.decoration ≠ 0 := r.realization.decoration_ne_zero 0

/-- The actual encounter list, including each selected relative degree. -/
def degreeItinerary (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) : List (Γ × J) :=
  List.ofFn fun j => (r.realization.1.val j, r.itinerary.get j)

/-- Recording degrees pairs each selected relative degree with its encounter. -/
theorem degreeItinerary_eq (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.degreeItinerary = List.ofFn fun j =>
      (r.realization.1.val j, r.itinerary.get j) := (rfl)

/-- Recording degrees retains every encounter. -/
@[simp]
theorem length_degreeItinerary (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.degreeItinerary.length = r.itinerary.length := by
  simp [degreeItinerary]

/-- Every actual decorated ray gives a member of the finite geometric inventory.
This derives realization from its actual path, rather than assuming a bound. -/
theorem degreeItinerary_mem (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.degreeItinerary ∈ realizedDegreeItineraries d f c v k := by
  obtain ⟨hpos, _, _⟩ := r.realization.2.eq_backwardRay
  have htrans := r.realization.2.transverse
  have hm (j : Fin r.itinerary.length) :
      r.realization.1.val j ∈ d.cutoff k ∧
        f (r.itinerary.get j) (v (r.realization.1.val j)) ≠ 0 := by
    exact ⟨r.degree_mem j, by simpa using htrans j⟩
  exact mem_realizedDegreeItineraries_ofFn d f c v k
    (fun j => (r.realization.1.val j, r.itinerary.get j)) hm r.degree_sub_mem Q
      (by simpa only [Fin.snoc_castSucc] using hpos)

/-- The number of encounters is bounded uniformly across all endpoints and
all coefficient histories at this cutoff. Identity encounters are included. -/
theorem length_le [Finite J]
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.itinerary.length ≤ Nat.card (d.cutoff k) * Nat.card J := by
  simpa only [length_degreeItinerary] using
    length_le_card_of_mem_realizedDegreeItineraries d f c v r.degreeItinerary_mem

/-- The itinerary and its decorated realization determine the cutoff ray.
The remaining fields carry only the cutoff and positive-shift proofs. -/
@[ext]
theorem ext {r s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q}
    (h : r.itinerary = s.itinerary) (hr : HEq r.realization s.realization) : r = s := by
  cases r
  cases s
  cases h
  cases hr
  rfl

/-- A nonstationary incoming direction makes every admitted ray proper. -/
theorem isProperMap (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hv : v 0 ≠ 0) (b : ℝ) : IsProperMap (fun t : Iic b => r.realization.2.ray t) :=
  r.realization.isProperMap hv b

end CutoffDecoratedRay

/-- The finite syntactic types at a cutoff: a bounded encounter word and a
surviving whole-component history with the allowed decreasing relative degrees.
The bound is derived for every actual ray by `CutoffDecoratedRay.length_le`. -/
structure CutoffDecoratedType (k : ℕ) where
  /-- All encounters, including those preserving the degree. -/
  itinerary : {l : List J // l.length ≤ Nat.card (d.cutoff k) * Nat.card J}
  /-- The nonzero history with the specified signs and normal velocities. -/
  history : (decoratedHistorySupport ℳ (fun j => T (itinerary.val.get j)) 0 a v
    (fun j => f (itinerary.val.get j)) (fun j => ε (itinerary.val.get j)) : Type _)
  /-- The selected relative degrees lie in the cutoff. -/
  degree_mem : ∀ j, history.val j ∈ d.cutoff k
  /-- Forward component shifts belong to the positive monoid. -/
  degree_sub_mem : ∀ i j, i ≤ j → history.val i - history.val j ∈ d.monoid

namespace CutoffDecoratedType

variable {d ℳ T a v f ε} {k : ℕ}

/-- A type is determined by its encounter word and its degree history. -/
@[ext]
theorem ext {t u : CutoffDecoratedType d ℳ T a v f ε k}
    (hl : t.itinerary = u.itinerary) (hh : HEq t.history u.history) : t = u := by
  cases t
  cases u
  cases hl
  cases hh
  rfl

/-- The whole final decoration determined by a type. -/
def decoration (t : CutoffDecoratedType d ℳ T a v f ε k) : M :=
  homogeneousHistory ℳ (fun j => T (t.itinerary.val.get j)) t.history.val a

/-- The final decoration is the history's whole output component. -/
@[simp]
theorem decoration_eq (t : CutoffDecoratedType d ℳ T a v f ε k) :
    t.decoration = homogeneousHistory ℳ (fun j => T (t.itinerary.val.get j))
      t.history.val a := (rfl)

/-- The complete geometric endpoint domain of a type, retaining avoidance of
unrecorded walls and singularities, as well as incoming-source admission. -/
def domain (t : CutoffDecoratedType d ℳ T a v f ε k) : Set V :=
  admissibleBackwardDomain (fun j => f (t.itinerary.val.get j))
    (fun j => c (t.itinerary.val.get j)) (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
    (fun j => P (t.itinerary.val.get j)) W S C

/-- Membership is the existing complete admissible backward endpoint condition. -/
@[simp]
theorem mem_domain (t : CutoffDecoratedType d ℳ T a v f ε k) (Q : V) :
    Q ∈ domain c P W S C t ↔ Q ∈
      admissibleBackwardDomain (fun j => f (t.itinerary.val.get j))
        (fun j => c (t.itinerary.val.get j))
        (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
        (fun j => P (t.itinerary.val.get j)) W S C := Iff.rfl

end CutoffDecoratedType

/-- There are finitely many cutoff types across all endpoints. This includes
arbitrarily many potential encounter words before the derived bound is imposed. -/
instance [Finite J] (k : ℕ) : Finite (CutoffDecoratedType d ℳ T a v f ε k) := by
  let I := {l : List J // l.length ≤ Nat.card (d.cutoff k) * Nat.card J}
  let : Finite I := (List.finite_length_le J _).to_subtype
  let g (t : CutoffDecoratedType d ℳ T a v f ε k) :
      Σ l : I, (decoratedHistorySupport ℳ (fun j => T (l.val.get j)) 0 a v
        (fun j => f (l.val.get j)) (fun j => ε (l.val.get j)) : Type _) :=
    ⟨t.itinerary, t.history⟩
  apply Finite.of_injective g
  intro t u h
  exact CutoffDecoratedType.ext (congrArg Sigma.fst h) (Sigma.mk.inj_iff.mp h).2

/-- Endpoint and type parameterize every actual cutoff ray, across all encounter
itineraries. No genericity hypothesis is required and coincident domains retain
separate types. -/
def cutoffDecoratedRayFiberEquiv [Finite J] (k : ℕ) (Q : V) :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q ≃
      {t : CutoffDecoratedType d ℳ T a v f ε k // Q ∈ CutoffDecoratedType.domain c P W S C t} where
  toFun r := ⟨⟨⟨r.itinerary, r.length_le⟩, r.realization.1, r.degree_mem,
    r.degree_sub_mem⟩, r.realization.2.mem_admissibleBackwardDomain⟩
  invFun t := ⟨t.val.itinerary.val, ⟨t.val.history,
    admissibleRayRealization _ _ _ _ _ _ _ _ t.property⟩,
    t.val.degree_mem, t.val.degree_sub_mem⟩
  left_inv r := by
    refine CutoffDecoratedRay.ext ?_ ?_
    · rfl
    exact heq_of_eq (congrArg (Sigma.mk r.realization.1) (Subsingleton.elim _ _))
  right_inv _ := rfl

/-- Forgetting the geometric realization retains the encounter word and its
entire degree history, together with the cutoff and positive-shift conditions. -/
@[simp]
theorem cutoffDecoratedRayFiberEquiv_apply_val [Finite J] (k : ℕ) (Q : V)
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val =
      ⟨⟨r.itinerary, r.length_le⟩, r.realization.1, r.degree_mem,
        r.degree_sub_mem⟩ := (rfl)

/-- The forward equivalence preserves the history indexed by the encounter word. -/
@[simp]
theorem cutoffDecoratedRayFiberEquiv_apply_history [Finite J] (k : ℕ) (Q : V)
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    HEq (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val.history
      r.realization.1 := (HEq.rfl)

/-- An admitted type is sent back to its unique admissible realization with
the same encounter word and degree history. -/
@[simp]
theorem cutoffDecoratedRayFiberEquiv_symm_apply [Finite J] (k : ℕ) (Q : V)
    (t : {t : CutoffDecoratedType d ℳ T a v f ε k //
      Q ∈ CutoffDecoratedType.domain c P W S C t}) :
    (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm t =
      ⟨t.val.itinerary.val, ⟨t.val.history,
        admissibleRayRealization _ _ _ _ _ _ _ _
          ((CutoffDecoratedType.mem_domain c P W S C t.val Q).mp t.property)⟩,
        t.val.degree_mem, t.val.degree_sub_mem⟩ := (rfl)

/-- Realizing an admitted type preserves its encounter-indexed degree history. -/
@[simp]
theorem cutoffDecoratedRayFiberEquiv_symm_apply_history [Finite J] (k : ℕ) (Q : V)
    (t : {t : CutoffDecoratedType d ℳ T a v f ε k //
      Q ∈ CutoffDecoratedType.domain c P W S C t}) :
    HEq ((cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm t).realization.1
      t.val.history := (HEq.rfl)

/-- The fiber equivalence preserves the final whole decoration. -/
@[simp↓] -- Compare decorations before expanding them into homogeneous histories.
theorem cutoffDecoratedRayFiberEquiv_decoration [Finite J] (k : ℕ) (Q : V)
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val.decoration =
      r.decoration := by
  rw [CutoffDecoratedRay.decoration, DecoratedAdmissibleRay.decoration_zero]
  rfl

/-- At any endpoint the full cutoff family has finitely many decorated rays,
without choosing or bounding the encounter itinerary beforehand. -/
instance [Finite J] (k : ℕ) (Q : V) :
    Finite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :=
  Finite.of_equiv _ (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm

/-- Zero incoming coefficient contributes no rays for any itinerary. -/
instance (k : ℕ) (Q : V) :
    IsEmpty (CutoffDecoratedRay d ℳ T (0 : ℳ 0) v f c ε P W S C k Q) :=
  ⟨fun r => isEmptyElim r.realization⟩

/-- Weighted evaluation over every admissible encounter itinerary at the cutoff. -/
def cutoffDecoratedEvaluation [Finite J] (k : ℕ) (Q : V) : M :=
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  ∑ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q, r.decoration

/-- The complete evaluation is the sum of final decorations over its actual
finite ray fiber. -/
theorem cutoffDecoratedEvaluation_def [Finite J] (k : ℕ) (Q : V) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
      ∑ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q, r.decoration := (rfl)

/-- Vanished incoming coefficient has zero total weighted evaluation. -/
@[simp]
theorem cutoffDecoratedEvaluation_zero [Finite J] (k : ℕ) (Q : V) :
    cutoffDecoratedEvaluation d ℳ T 0 v f c ε P W S C k Q = 0 := by
  simp [cutoffDecoratedEvaluation]

open Classical in
/-- Total evaluation is the finite sum over all cutoff types whose complete
endpoint domains admit the endpoint, with their whole final decorations. -/
theorem cutoffDecoratedEvaluation_eq_sum [Finite J] (k : ℕ) (Q : V) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      let := Fintype.ofFinite (CutoffDecoratedType d ℳ T a v f ε k)
      ∑ t : CutoffDecoratedType d ℳ T a v f ε k,
        if Q ∈ CutoffDecoratedType.domain c P W S C t then t.decoration else 0 := by
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  let := Fintype.ofFinite (CutoffDecoratedType d ℳ T a v f ε k)
  rw [cutoffDecoratedEvaluation]
  trans ∑ t : {t : CutoffDecoratedType d ℳ T a v f ε k //
    Q ∈ CutoffDecoratedType.domain c P W S C t},
    t.val.decoration
  · exact Fintype.sum_equiv (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q)
      _ _ (fun r => (cutoffDecoratedRayFiberEquiv_decoration d ℳ T a v f c ε P W S C k Q r).symm)
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (p := fun t : CutoffDecoratedType d ℳ T a v f ε k =>
        Q ∈ CutoffDecoratedType.domain c P W S C t)
      (Finset.univ.filter fun t : CutoffDecoratedType d ℳ T a v f ε k =>
      Q ∈ CutoffDecoratedType.domain c P W S C t) (by simp) (fun t => t.decoration)).symm

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite J] [Finite K]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC

/-- One finite exceptional arrangement controls every encounter itinerary at the
cutoff. All type-domain frontiers are exceptional, and nearby actual ray fibers
are bijective with the same whole decorations. -/
theorem exists_cutoffDecoratedRay_membershipArrangement (k : ℕ) :
    ∃ E : ExceptionalArrangement V,
      (∀ t : CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k,
        frontier (CutoffDecoratedType.domain c P W S C t) ⊆ {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
        ∃ e : CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q ≃
            CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q',
          ∀ r, (e r).itinerary = r.itinerary ∧ (e r).decoration = r.decoration := by
  have hdom (t : CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k) :
      IsRationalSemilinear h (CutoffDecoratedType.domain c P W S C t) :=
    isRationalSemilinear_admissibleBackwardDomain
      (fun j => f (t.itinerary.val.get j)) (fun j => c (t.itinerary.val.get j))
      (fun j => P (t.itinerary.val.get j)) W S C
      (fun j => w (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
      (fun j => hf _) (fun j => hP _) hW hS hC
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement hdom
  refine ⟨E, hfrontier, fun Q hQ => (hstable Q hQ).mono fun Q' hQQ' => ?_⟩
  let eQ (Q : V) := cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q))
    f c ε P W S C k Q
  let e := (eQ Q).trans ((Equiv.subtypeEquivRight (fun t => (hQQ' t).symm)).trans
    (eQ Q').symm)
  refine ⟨e, fun r => ?_⟩
  have he : (eQ Q' (e r)).val = (eQ Q r).val := by simp [e]
  refine ⟨congrArg (fun t => t.itinerary.val) he, ?_⟩
  calc
    (e r).decoration = (eQ Q' (e r)).val.decoration :=
      (cutoffDecoratedRayFiberEquiv_decoration d ℳ T a (fun q => i (w q))
        f c ε P W S C k Q' (e r)).symm
    _ = (eQ Q r).val.decoration := congrArg CutoffDecoratedType.decoration he
    _ = r.decoration := cutoffDecoratedRayFiberEquiv_decoration d ℳ T a
      (fun q => i (w q)) f c ε P W S C k Q r

/-- Weighted evaluation over the complete cutoff family is locally constant off
one finite exceptional arrangement, over arbitrary semirings. -/
theorem exists_cutoffDecoratedEvaluation_eventually_eq (k : ℕ) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q → ∀ᶠ Q' in nhds Q,
      cutoffDecoratedEvaluation d ℳ T a (fun q => i (w q)) f c ε P W S C k Q' =
        cutoffDecoratedEvaluation d ℳ T a (fun q => i (w q)) f c ε P W S C k Q := by
  obtain ⟨E, _, hstable⟩ := exists_cutoffDecoratedRay_membershipArrangement d ℳ T a
    f c ε P W S C h w hf hP hW hS hC k
  refine ⟨E, fun Q hQ => (hstable Q hQ).mono fun Q' ⟨e, he⟩ => ?_⟩
  let := Fintype.ofFinite
    (CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q)
  let := Fintype.ofFinite
    (CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q')
  exact (Fintype.sum_equiv e _ _ (fun r => (he r).2.symm)).symm

end Rational

end Mei
