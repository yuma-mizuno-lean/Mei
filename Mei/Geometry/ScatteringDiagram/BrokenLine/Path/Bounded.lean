/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import TauCeti.Combinatorics.Quiver.BoundedPaths

/-!
# Exhaustive closed families across different chambers

An encounter bound in a finite quiver turns the finite-inventory closed ray
charts into an exhaustive family of actual decorated rays. The resulting
equivalence ranges over all encounter paths, with no length restriction in its
target. It retains the endpoint, entire encounter path and component history,
and hence the whole geometric ray and incoming tail. Closed chart extensions
remain proper and preserve admission to the original global source.

Weighted evaluation is independent of the exhaustive inventory. Thus a numerical
bound is only a device for constructing a finite family, rather than part of the
mathematical ray fiber. Intermediate chamber modules and degree types may differ;
spatially coincident histories and unchanged-degree encounters remain distinct.

The construction uses `TauCeti.Quiver.finite_boundedPaths`,
`Equiv.sigmaSubtypeEquivOfSubset` and `exists_pathDecoratedFamily_closedCharts`.
The finite encounter-tree interpretation follows Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, Proposition
3.5 and Lemma 3.7 (arXiv:1601.07081v4); closed endpoint charts follow
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "Ray" p:max X:max => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X

variable [Finite Q] [∀ q q' : Q, Finite (q ⟶ q')]

/-- An encounter bound makes the unrestricted varying-chamber ray fiber finite.
No positive grading, finite set of degrees or finite-dimensional coefficient
module is required. The bound concerns actual rays, including their source and
avoidance conditions. -/
theorem finite_pathDecoratedRays_of_encounter_bound (L : ℕ) (X : V)
    (hbound : ∀ p : Path a b, Ray p X → p.length ≤ L) :
    Finite (Σ p : Path a b, Ray p X) := by
  have : Finite {p : Path a b // p.length ≤ L} :=
    TauCeti.Quiver.finite_boundedPaths L a b
  exact Finite.of_equiv _
    (Equiv.sigmaSubtypeEquivOfSubset (fun p => Ray p X) (fun p => p.length ≤ L) hbound)

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "Types" s:max => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "dirs" t:max => Path.Degrees.reverseVertexLabels vel i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t))
local notation "D" t:max => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "path" t:max => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
local notation "Rays" X:max => Σ p : Path a b,
  PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X

omit [Finite Q] [∀ q q' : Q, Finite (q ⟶ q')] in
include hν hP hW hS hC in
/-- Finite closed charts for the inventory `s` exhaust all actual varying-chamber rays
whenever every actual ray has its encounter path in `s`. Closed endpoints keep their
continuous whole paths and incoming-source admission, including collapsed and singular
limits; boundary admissibility and the classification of boundary events are not
asserted. -/
theorem exists_pathDecoratedRay_closedCharts_of_forall_mem (s : Finset (Path a b))
    (hs : ∀ X (p : Path a b),
      PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X → p ∈ s) :
    ∃ (κ : Types s → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
      (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
        A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
        IsProperMap (fun X : A t j => (path t) X.val) ∧
        ∀ X ∈ A t j, (path t) X 0 = X ∧
          (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
          (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
      (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
        (intrinsicInterior ℝ (A t k))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
      ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃ (Σ X, Rays X),
        (∀ z, (E z).1 = z.2.2.val) ∧
        (∀ z, (E z).2.1 = z.1.1.val) ∧
        (∀ z, HEq (E z).2.2.1 z.1.2) ∧
        ∀ z, (E z).2.2.decoration = z.1.1.val.homogeneousHistory T ℳ z.1.2.val x := by
  obtain ⟨κ, hκ, A, hA, hdisj, hcover, E, hX, ht⟩ :=
    exists_pathDecoratedFamily_closedCharts T ℳ i₀ x s ν ε c P W S C
      h w hν hP hW hS hC
  let e (X : V) := Equiv.sigmaSubtypeEquivOfSubset
    (fun p => PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X)
    (fun p => p ∈ s) (hs X)
  refine ⟨κ, hκ, A, hA, hdisj, hcover, E.trans (Equiv.sigmaCongrRight e), hX, ?_, ?_, ?_⟩
  · intro z
    exact congrArg (fun t : Types s => t.1.val) (ht z)
  · intro z
    exact (Sigma.mk.inj_iff.mp (ht z)).2
  · intro z
    rw [PathDecoratedRay.decoration_def]
    exact congrArg (fun t : Types s => t.1.val.homogeneousHistory T ℳ t.2.val x) (ht z)

include hν hP hW hS hC in
/-- An encounter bound constructs exhaustive finite closed charts for all actual
varying-chamber rays. Closed endpoints keep their continuous whole paths and
incoming-source admission, including collapsed and singular limits; boundary
admissibility and the classification of boundary events are not asserted. -/
theorem exists_exhaustive_pathDecoratedFamily_closedCharts (L : ℕ)
    (hbound : ∀ X (p : Path a b),
      PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X → p.length ≤ L) :
    ∃ s : Finset (Path a b),
      (∀ X (p : Path a b),
        PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X → p ∈ s) ∧
      ∃ (κ : Types s → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
        (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
          IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
          A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
          IsProperMap (fun X : A t j => (path t) X.val) ∧
          ∀ X ∈ A t j, (path t) X 0 = X ∧
            (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
            (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
        (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
          (intrinsicInterior ℝ (A t k))) ∧
        (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
        ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃ (Σ X, Rays X),
          (∀ z, (E z).1 = z.2.2.val) ∧
          (∀ z, (E z).2.1 = z.1.1.val) ∧
          (∀ z, HEq (E z).2.2.1 z.1.2) ∧
          ∀ z, (E z).2.2.decoration = z.1.1.val.homogeneousHistory T ℳ z.1.2.val x := by
  have : Finite {p : Path a b // p.length ≤ L} :=
    TauCeti.Quiver.finite_boundedPaths L a b
  let s := (Set.toFinite {p : Path a b | p.length ≤ L}).toFinset
  have hs (X : V) (p : Path a b)
      (r : PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X) : p ∈ s := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hbound X p r
  exact ⟨s, hs, exists_pathDecoratedRay_closedCharts_of_forall_mem T ℳ i₀ x ν ε c P W S C
    h w hν hP hW hS hC s hs⟩

end Rational

end Mei
