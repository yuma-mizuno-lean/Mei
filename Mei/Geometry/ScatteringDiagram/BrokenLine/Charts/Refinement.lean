/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification.Refinement
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration

/-!
# Common refinements of closed decorated-ray charts

Two finite semilinear subdivisions of each complete decorated type's endpoint
domain admit common closed polyhedral charts. Each new interior refines both
subdivisions; its closure lies in both parent closures and in the closed type
domain. The same type path extends over every new chart, so refinements preserve
the full global history, incoming tail, encounter data and whole decoration.
In particular the weighted sum is independent of these chart subdivisions.

The construction uses the common semilinear refinement theorem and
`CutoffDecoratedType.path`, rather than reconstructing paths in a restricting
endpoint set. Boundary paths may have collapsed or singular encounters and are
not asserted to be admissible. This is the endpoint-chart viewpoint of
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Mei.Convex

namespace Mei

variable {R M Γ V J K Λ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ} [Finite J]
  (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)
  [AddCommGroup Λ] {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "domain" t => CutoffDecoratedType.domain c P W S C t

open Classical in
/-- Common closed charts for two subdivisions of the actual complete type
domains. The refined interiors exhaust every original piece separately and
partition the actual rays without changing their weights. The closed path maps
are proper; each boundary path retains its incoming direction and source tail.
The source need only be a rational-normal polyhedron, and no rationality of
velocities is needed once the endpoint subdivisions are supplied. -/
theorem exists_cutoffDecoratedRay_common_closedCharts
    (hC : IsRationalNormalPolyhedron h C)
    (ι κ : Types → Type*) [∀ t, Finite (ι t)] [∀ t, Finite (κ t)]
    (A : ∀ t, ι t → Set V) (B : ∀ t, κ t → Set V)
    (hA : ∀ t j, IsRationalSemilinear h (A t j))
    (hB : ∀ t j, IsRationalSemilinear h (B t j))
    (hAdisj : ∀ t, Pairwise fun j l => Disjoint (A t j) (A t l))
    (hBdisj : ∀ t, Pairwise fun j l => Disjoint (B t j) (B t l))
    (hAcover : ∀ t, ⋃ j, A t j = domain t)
    (hBcover : ∀ t, ⋃ j, B t j = domain t) :
    ∃ (μ : Types → Type) (_ : ∀ t, Fintype (μ t))
      (D : ∀ t, μ t → Set V) (left : ∀ t, μ t → ι t) (right : ∀ t, μ t → κ t),
      (∀ t j, (D t j).Nonempty ∧ IsRationalNormalPolyhedron h (D t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (D t j)) ∧
        intrinsicInterior ℝ (D t j) ⊆ A t (left t j) ∩ B t (right t j) ∧
        D t j ⊆ closure (A t (left t j)) ∩ closure (B t (right t j)) ∧
        D t j ⊆ closure (domain t) ∧
        IsProperMap (fun Q : D t j => t.path c Q.val) ∧
        ∀ Q ∈ D t j,
          (∀ᶠ s : ℝ in atBot, t.path c Q s ∈ C) ∧
          ∃ β : FiniteAffineRay V V, β.endpoint = Q ∧ β.incomingDirection = v 0 ∧
            ∀ s : ℝ, s ≤ 0 → β s = t.path c Q s) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (D t j))
        (intrinsicInterior ℝ (D t l))) ∧
      (∀ t j, ⋃ (s) (_ : left t s = j), intrinsicInterior ℝ (D t s) = A t j) ∧
      (∀ t j, ⋃ (s) (_ : right t s = j), intrinsicInterior ℝ (D t s) = B t j) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (D t j) = domain t) ∧
      (∀ Q, cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
        let := Fintype.ofFinite Types
        ∑ t : Types, ∑ j : μ t,
          if Q ∈ intrinsicInterior ℝ (D t j) then t.decoration else 0) ∧
      ∃ e : (Σ t, Σ j : μ t, intrinsicInterior ℝ (D t j)) ≃
          (Σ Q, CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q),
        (∀ z, (e z).1 = z.2.2.val) ∧
        (∀ z, (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C
          k (e z).1 (e z).2).val = z.1) ∧
        (∀ z, (e z).2.decoration = z.1.decoration) ∧
        ∀ z, (e z).2.realization.2.ray.toContinuousMap =
          z.1.path c z.2.2.val := by
  classical
  have hex (t : Types) := IsRationalSemilinear.exists_common_polyhedralRefinement
    (hA t) (hB t) (hAdisj t) (hBdisj t) ((hAcover t).trans (hBcover t).symm)
  choose μ hμ D left right hD hdisj hleft hright using hex
  let (t : Types) : Fintype (μ t) := @Fintype.ofFinite _ (hμ t)
  have hdomain (t : Types) : ⋃ j, intrinsicInterior ℝ (D t j) = domain t := by
    apply Subset.antisymm
    · intro Q hQ
      obtain ⟨j, hj⟩ := mem_iUnion.mp hQ
      rw [← hAcover t]
      exact mem_iUnion.mpr ⟨left t j, (hD t j).2.2.2.2.1 hj |>.1⟩
    · intro Q hQ
      obtain ⟨j, hj⟩ := mem_iUnion.mp ((hAcover t).symm ▸ hQ)
      obtain ⟨s, -, hs⟩ := mem_iUnion₂.mp ((hleft t j).symm ▸ hj)
      exact mem_iUnion.mpr ⟨s, hs⟩
  refine ⟨μ, inferInstance, D, left, right, ?_, hdisj, hleft, hright, hdomain, ?_, ?_⟩
  · intro t j
    obtain ⟨hne, hpoly, -, hlc, hsub, hclosure⟩ := hD t j
    have hsubdomain : D t j ⊆ closure (domain t) := by
      apply (hclosure.trans inter_subset_left).trans (closure_mono ?_)
      rw [← hAcover t]
      exact subset_iUnion (A t) (left t j)
    exact ⟨hne, hpoly, hlc, hsub, hclosure, hsubdomain,
      t.isProperMap_path_restrict_and_exists_limitRay c P W S C hC hpoly.isClosed hsubdomain⟩
  · intro Q
    exact cutoffDecoratedEvaluation_eq_sum_charts d ℳ T a v f c ε P W S C
      k μ (fun t j => intrinsicInterior ℝ (D t j)) hdisj hdomain Q
  -- Reindex the exact global ray fiber, retaining its complete type. No paths
  -- are constructed afresh on a chart or on an endpoint restriction.
  · let e := (Set.sigmaDisjointCoverEquiv hdisj hdomain).trans
      (Equiv.sigmaCongrRight fun Q =>
        (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q).symm)
    have hendpoint (z) : (e z).1 = z.2.2.val := by
      simp only [e, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Set.sigmaDisjointCoverEquiv_apply_fst]
    have he (z) : e z = ⟨z.2.2.val,
        (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k z.2.2.val).symm
          ⟨z.1, hdomain z.1 ▸ mem_iUnion.mpr ⟨z.2.1, z.2.2.property⟩⟩⟩ := by
      dsimp only [e]
      rw [Equiv.trans_apply, Set.sigmaDisjointCoverEquiv_apply, Equiv.sigmaCongrRight_apply]
    have htype (z) : (cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C
        k (e z).1 (e z).2).val = z.1 := by
      rw [he]
      exact congrArg Subtype.val
        ((cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k _).apply_symm_apply _)
    refine ⟨e, hendpoint, htype, fun z => ?_, fun z => ?_⟩
    · exact (cutoffDecoratedRayFiberEquiv_decoration d ℳ T a v f c ε P W S C
        k (e z).1 (e z).2).symm.trans (congrArg CutoffDecoratedType.decoration (htype z))
    · rw [CutoffDecoratedRay.toContinuousMap_eq_typePath c P W S C, htype, hendpoint]

end Mei
