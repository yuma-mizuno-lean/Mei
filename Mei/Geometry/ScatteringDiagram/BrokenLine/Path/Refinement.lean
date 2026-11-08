/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
import Mei.Algebra.BigOperators.Group.Finset.Indicator
import Mei.Geometry.Convex.Polyhedron.Rational.Stratification.Cover
import Mei.Geometry.Convex.Polyhedron.Rational.Stratification.Refinement

/-!
# Subdividing closed charts of varying-chamber decorated rays

The finite closed charts of a finite itinerary inventory subdivide each complete type's
endpoint domain. Two such subdivisions have common closed polyhedral charts, and a finite
overlapping cover of the endpoint space has charts subordinate to it. Every new interior
parameterizes the same actual rays, with their entire encounter paths, component histories
and incoming tails; only the endpoint domains are subdivided, and no path is rebuilt on a
chart. Since each closed chart lies in the closure of the original type domain, it carries the
original whole-path extension, which is proper in the endpoint and retains
incoming-source admission. Boundary paths are not asserted admissible.

Chamber modules and degree types may differ along the path. The weighted evaluation of the
rays through every endpoint is the sum of the final decorations over any disjoint cover of
the type domains, so it is independent of the chosen subdivision. The statements follow those
for a single chamber module in `Mei.Geometry.ScatteringDiagram.BrokenLine.Charts.Refinement`
and `Mei.Geometry.ScatteringDiagram.BrokenLine.Charts.Cover`. Closed charts of the endpoint
domains are those of Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
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
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀) (s : Finset (Path a b))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

section General

local notation "Labels" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "dirs" => (fun t : Labels => Path.Degrees.reverseVertexLabels v i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "D" => (fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C)

open Classical in
/-- The weighted evaluation of the actual rays through any endpoint is the sum of the final
decorations over every chart whose endpoint piece contains it, for any disjoint cover of each
complete type's domain. In particular it does not depend on the subdivision. -/
theorem pathDecoratedEvaluation_eq_sum_charts {κ : Labels → Type*} [∀ t, Fintype (κ t)]
    (B : ∀ t, κ t → Set V) (hdisj : ∀ t, Pairwise fun j l => Disjoint (B t j) (B t l))
    (hcover : ∀ t, ⋃ j, B t j = D t) (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X =
      let := Fintype.ofFinite Labels
      ∑ t : Labels, ∑ j : κ t,
        if X ∈ B t j then t.1.val.homogeneousHistory T ℳ t.2.val x else 0 := by
  rw [pathDecoratedEvaluation_eq_sum_domains T ℳ i₀ x s v ν ε c P W S C]
  exact Finset.sum_congr rfl fun t _ => Set.ite_mem_eq_sum_of_pairwise_disjoint (B t)
    (hdisj t) (hcover t) X _

end General

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "Labels" => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "dirs" => (fun t : Labels => Path.Degrees.reverseVertexLabels vel i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "D" => (fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C)
local notation "path" => (fun t : Labels => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t))

include hν hP hW hS hC

/-- Two subdivisions of the endpoint domains of the complete types have common closed
polyhedral charts. Each new interior lies in one piece of each subdivision and exhausts it,
and the whole-path extension of the type is proper on the closed chart. The interiors
parameterize exactly the actual rays through the itinerary inventory, retaining each
encounter path and component history. -/
theorem exists_pathDecoratedFamily_common_closedCharts
    (ι' κ : Labels → Type*) [∀ t, Finite (ι' t)] [∀ t, Finite (κ t)]
    (A : ∀ t, ι' t → Set V) (B : ∀ t, κ t → Set V)
    (hA : ∀ t j, IsRationalSemilinear h (A t j))
    (hB : ∀ t j, IsRationalSemilinear h (B t j))
    (hAdisj : ∀ t, Pairwise fun j l => Disjoint (A t j) (A t l))
    (hBdisj : ∀ t, Pairwise fun j l => Disjoint (B t j) (B t l))
    (hAcover : ∀ t, ⋃ j, A t j = D t) (hBcover : ∀ t, ⋃ j, B t j = D t) :
    ∃ (μ : Labels → Type) (_ : ∀ t, Finite (μ t)) (E : ∀ t, μ t → Set V)
      (left : ∀ t, μ t → ι' t) (right : ∀ t, μ t → κ t),
      (∀ t j, (E t j).Nonempty ∧ IsRationalNormalPolyhedron h (E t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (E t j)) ∧
        intrinsicInterior ℝ (E t j) ⊆ A t (left t j) ∩ B t (right t j) ∧
        E t j ⊆ closure (A t (left t j)) ∩ closure (B t (right t j)) ∧
        E t j ⊆ closure (D t) ∧ IsProperMap (fun X : E t j => (X : V)) ∧
        IsProperMap (fun X : E t j => (path t) X.val) ∧
        ∀ X ∈ E t j, (path t) X 0 = X ∧ (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
          (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (E t j))
        (intrinsicInterior ℝ (E t l))) ∧
      (∀ t j, ⋃ (u) (_ : left t u = j), intrinsicInterior ℝ (E t u) = A t j) ∧
      (∀ t j, ⋃ (u) (_ : right t u = j), intrinsicInterior ℝ (E t u) = B t j) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (E t j) = D t) ∧
      ∃ e : (Σ t, Σ j : μ t, intrinsicInterior ℝ (E t j)) ≃
          (Σ X, Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X),
        (∀ z, (e z).1 = z.2.2.val) ∧
          ∀ z, (⟨(e z).2.1, (e z).2.2.1⟩ : Labels) = z.1 := by
  classical
  choose μ hμ E left right hE hdisj hleft hright using fun t =>
    IsRationalSemilinear.exists_common_polyhedralRefinement (hA t) (hB t) (hAdisj t) (hBdisj t)
      ((hAcover t).trans (hBcover t).symm)
  have hcover (t : Labels) : ⋃ j, intrinsicInterior ℝ (E t j) = D t := by
    rw [← hAcover t]
    refine Subset.antisymm (iUnion_subset fun j => ?_) (iUnion_subset fun j => ?_)
    · exact ((hE t j).2.2.2.2.1.trans inter_subset_left).trans
        (subset_iUnion (A t) (left t j))
    · rw [← hleft t j]
      exact iUnion₂_subset fun u _ => subset_iUnion (fun u => intrinsicInterior ℝ (E t u)) u
  refine ⟨μ, hμ, E, left, right, fun t j => ?_, hdisj, hleft, hright, hcover,
    pathDecoratedChartEquiv T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hcover,
    pathDecoratedChartEquiv_apply_fst T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hcover,
    pathDecoratedChartEquiv_apply_type T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hcover⟩
  obtain ⟨hne, hpoly, -, hlc, hsub, hclosure⟩ := hE t j
  have hsubD : E t j ⊆ closure (D t) := by
    refine (hclosure.trans inter_subset_left).trans (closure_mono ?_)
    rw [← hAcover t]
    exact subset_iUnion (A t) (left t j)
  exact ⟨hne, hpoly, hlc, hsub, hclosure, hsubD, hpoly.isClosed.isProperMap_subtypeVal,
    pathDecoratedType_closedChart T ℳ i₀ x s ν ε c P W S C h w hC t hpoly hsubD⟩

/-- A finite overlapping cover of the endpoint space has closed polyhedral charts, indexed by
the complete types, that are subordinate to it. Their interiors partition each type domain,
each lies in or misses every patch, and those inside a patch exhaust the type's restriction to
it. The whole-path extension is proper on each closed chart, and the interiors parameterize
every actual ray of the itinerary inventory exactly once, even over patch overlaps. -/
theorem exists_pathDecoratedFamily_cover_closedCharts
    {ι' : Type*} [Finite ι'] (U : ι' → Set V) (hU : ∀ j, IsRationalSemilinear h (U j))
    (hcover : ∀ t : Labels, D t ⊆ ⋃ j, U j) :
    ∃ (κ : Labels → Type) (_ : ∀ t, Finite (κ t)) (B : ∀ t, κ t → Set V)
      (patch : ∀ t, κ t → ι'),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        intrinsicInterior ℝ (B t j) ⊆ D t ∩ U (patch t j) ∧
        B t j ⊆ closure (D t ∩ U (patch t j)) ∧ B t j ⊆ closure (D t) ∧
        IsProperMap (fun X : B t j => (X : V)) ∧
        IsProperMap (fun X : B t j => (path t) X.val) ∧
        ∀ X ∈ B t j, (path t) X 0 = X ∧ (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
          (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = D t) ∧
      (∀ t j u, intrinsicInterior ℝ (B t j) ⊆ U u ∨
        Disjoint (intrinsicInterior ℝ (B t j)) (U u)) ∧
      (∀ t u, ⋃ (j) (_ : intrinsicInterior ℝ (B t j) ⊆ U u),
        intrinsicInterior ℝ (B t j) = D t ∩ U u) ∧
      ∃ e : (Σ t, Σ j : κ t, intrinsicInterior ℝ (B t j)) ≃
          (Σ X, Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X),
        (∀ z, (e z).1 = z.2.2.val) ∧
          ∀ z, (⟨(e z).2.1, (e z).2.2.1⟩ : Labels) = z.1 := by
  classical
  choose κ hκ B patch hB hdisj hBcover hmem hpatch using fun t : Labels =>
    (isRationalSemilinear_pathDecoratedDomain
      i₀ ν c P W S C h w hν hP hW hS hC t.1.val t.2.val
      ).exists_cover_polyhedralCharts U hU (hcover t)
  refine ⟨κ, hκ, B, patch, fun t j => ?_, hdisj, hBcover, hmem, hpatch,
    pathDecoratedChartEquiv T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hBcover,
    pathDecoratedChartEquiv_apply_fst T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hBcover,
    pathDecoratedChartEquiv_apply_type T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC hdisj hBcover⟩
  obtain ⟨hne, hpoly, -, hlc, hsub, hclosure⟩ := hB t j
  have hsubD : B t j ⊆ closure (D t) := hclosure.trans (closure_mono inter_subset_left)
  exact ⟨hne, hpoly, hlc, hsub, hclosure, hsubD, hpoly.isClosed.isProperMap_subtypeVal,
    pathDecoratedType_closedChart T ℳ i₀ x s ν ε c P W S C h w hC t hpoly hsubD⟩

end Rational

end Mei
