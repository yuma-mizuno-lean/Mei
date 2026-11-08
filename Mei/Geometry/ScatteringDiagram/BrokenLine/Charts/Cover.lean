/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification.Cover
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic

/-!
# Closed decorated-ray charts on endpoint covers

Finite semilinear endpoint covers, including overlapping patches, admit closed
polyhedral charts indexed by the original complete decorated types. Their
interiors partition each full type domain. Every chart chooses one patch and is
compatible with all other patches. Selecting the charts whose relative interiors
lie in a patch and taking the union of those interiors recovers exactly the
restricted type domain. Hence overlap endpoints contribute
once to the global weighted evaluation.

The closed charts carry the original global path extension, including its
incoming tail. Paths are not rebuilt inside a patch. Their closures lie in the
closure of the type domain intersected with the chosen patch, which need not
be the intersection of those two closures. Boundary paths are not asserted to
be admissible. The closed-family viewpoint follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

variable {R M Γ V J K Λ ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ} [Finite J] [Finite ι]
  (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)
  [AddCommGroup Λ] {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "domain" t => CutoffDecoratedType.domain c P W S C t

open Classical in
/-- A finite overlapping endpoint cover has a common disjoint subdivision of
all complete decorated types. Each original ray has its endpoint in exactly one
chart relative interior of its type; patch restriction selects these same interiors
and global paths.
Weighted evaluation counts each ray once, even on overlaps. -/
theorem exists_cutoffDecoratedRay_cover_closedCharts
    (hD : ∀ t : Types, IsRationalSemilinear h (domain t))
    (hC : IsRationalNormalPolyhedron h C)
    (U : ι → Set V) (hU : ∀ j, IsRationalSemilinear h (U j))
    (hcover : ∀ t : Types, (domain t) ⊆ ⋃ j, U j) :
    ∃ (κ : Types → Type) (_ : ∀ t, Fintype (κ t))
      (B : ∀ t, κ t → Set V) (patch : ∀ t, κ t → ι),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        intrinsicInterior ℝ (B t j) ⊆ (domain t) ∩ U (patch t j) ∧
        B t j ⊆ closure ((domain t) ∩ U (patch t j)) ∧
        IsProperMap (fun Q : B t j => t.path c Q.val) ∧
        ∀ Q ∈ B t j, (∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C) ∧
          ∃ β : FiniteAffineRay V V, β.endpoint = Q ∧ β.incomingDirection = v 0 ∧
            ∀ s : ℝ, s ≤ 0 → β s = t.path c Q s) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = domain t) ∧
      (∀ t j u, intrinsicInterior ℝ (B t j) ⊆ U u ∨
        Disjoint (intrinsicInterior ℝ (B t j)) (U u)) ∧
      (∀ t u, ⋃ (j) (_ : intrinsicInterior ℝ (B t j) ⊆ U u),
        intrinsicInterior ℝ (B t j) = (domain t) ∩ U u) ∧
      (∀ Q, cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
        let := Fintype.ofFinite Types
        ∑ t : Types, ∑ j : κ t,
          if Q ∈ intrinsicInterior ℝ (B t j) then t.decoration else 0) ∧
      ∀ Q (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q),
        let t := (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val
        ∃! j : κ t, Q ∈ intrinsicInterior ℝ (B t j) ∧
          r.realization.2.ray.toContinuousMap = t.path c Q := by
  classical
  have hex (t : Types) := (hD t).exists_cover_polyhedralCharts U hU (hcover t)
  choose κ hκ B patch hB hdisj hBcover hmem hpatch using hex
  let (t : Types) : Fintype (κ t) := @Fintype.ofFinite _ (hκ t)
  refine ⟨κ, inferInstance, B, patch, ?_, hdisj, hBcover, hmem, hpatch, ?_, ?_⟩
  · intro t j
    obtain ⟨hne, hpoly, -, hlc, hsub, hclosure⟩ := hB t j
    have hglobal : B t j ⊆ closure (domain t) :=
      hclosure.trans (closure_mono inter_subset_left)
    exact ⟨hne, hpoly, hlc, hsub, hclosure,
      (t.isProperMap_path_closure c P W S C).comp
        (Topology.IsClosedEmbedding.inclusion hglobal
          (hpoly.isClosed.preimage continuous_subtype_val)).isProperMap,
      fun Q hQ => ⟨t.path_eventually_mem c P W S C hC (hglobal hQ),
        t.exists_limitRay c P W S C (hglobal hQ)⟩⟩
  · exact cutoffDecoratedEvaluation_eq_sum_charts d ℳ T a v f c ε P W S C
      k κ (fun t j => intrinsicInterior ℝ (B t j)) hdisj hBcover
  · intro Q r
    let t := (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).val
    have hQ : Q ∈ domain t :=
      (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q r).property
    obtain ⟨j, hj⟩ := mem_iUnion.mp ((hBcover t).symm ▸ hQ)
    refine ⟨j, ⟨hj, r.toContinuousMap_eq_typePath c P W S C⟩, ?_⟩
    intro l hl
    by_contra hlj
    exact disjoint_left.mp (hdisj t hlj) hl.1 hj

end Mei
