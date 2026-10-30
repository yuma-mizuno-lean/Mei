/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Perturbation

/-!
# Common paths preserving wall-family products

Two admissible paths with the same ambient vertex list can be moved into any
countable collection of finite polyhedral wall families while retaining both
products. The original endpoints need not avoid the additional walls. Stationary
segments supply interior vertices even for constant test paths. The groups and
the index universes of the two tests may differ.

This extracts the common-test argument of
`DirectedDiagram.exists_common_levelPathProduct_eq` to arbitrary wall families.
It combines `Quiver.Path.exists_pos_wallPathProduct_eq_of_forall₂_dist_lt` with
`CommonWallComplement.exists_forall₂_dist_lt_free_endpoints`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Quiver.Path

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Group G] {W : ι → Set V}

variable {κ H J : Type*} {I : J → Type*} [Finite κ] [Group H]
  [FiniteDimensional ℝ V] [Countable J] [∀ j, Finite (I j)]
  {U : κ → Set V} {A : ∀ j, I j → Set V}

/-- Replace two tests sharing their ambient vertices by a path admissible for a
countable collection of finite wall families. Every realization of the new vertices
in either original family has that test's original product. Both endpoints may move. -/
theorem exists_common_wallPathProduct_eq
    (hclosedW : ∀ i, IsClosed (W i))
    (hdimW : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 =
      Module.finrank ℝ V)
    (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (label : ι → G)
    (commW : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) →
      Commute (label i) (label j))
    (hclosedU : ∀ i, IsClosed (U i))
    (hdimU : ∀ i, Module.finrank ℝ (affineSpan ℝ (U i)).direction + 1 =
      Module.finrank ℝ V)
    (μ : κ → V →ₗ[ℝ] ℝ)
    (hμ : ∀ i, LinearMap.ker (μ i) = (affineSpan ℝ (U i)).direction)
    (labelU : κ → H)
    (commU : ∀ i j, affineSpan ℝ (U i) = affineSpan ℝ (U j) →
      Commute (labelU i) (labelU j))
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (A j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (A j i)).direction + 1 =
      Module.finrank ℝ V)
    {x y : WallComplement W} {x' y' : WallComplement U}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    ∃ (a b : CommonWallComplement A) (r : Quiver.Path a b),
      (∀ {u v : WallComplement W} (s : AdmissiblePLPath u v),
        s.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val →
          s.wallPathProduct ν label commW = p.wallPathProduct ν label commW) ∧
      (∀ {u v : WallComplement U} (s : AdmissiblePLPath u v),
        s.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val →
          s.wallPathProduct μ labelU commU = q.wallPathProduct μ labelU commU) := by
  obtain ⟨p', hvp, hprodP⟩ := p.exists_vertices_eq_cons_wallPathProduct_eq hclosedW ν label commW
  obtain ⟨q', hvq, hprodQ⟩ := q.exists_vertices_eq_cons_wallPathProduct_eq hclosedU μ labelU commU
  have hx : x.val = x'.val := by simpa using congrArg List.head? hpq
  have hvpq : p'.vertices.map WallComplement.val = q'.vertices.map WallComplement.val := by
    rw [hvp, hvq, hx, hpq]
  obtain ⟨ε₁, hε₁, hp⟩ := p'.exists_pos_wallPathProduct_eq_of_forall₂_dist_lt
    hclosedW hdimW ν hν label commW
  obtain ⟨ε₂, hε₂, hq⟩ := q'.exists_pos_wallPathProduct_eq_of_forall₂_dist_lt
    hclosedU hdimU μ hμ labelU commU
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [y.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  obtain ⟨a, b, r, hr⟩ := CommonWallComplement.exists_forall₂_dist_lt_free_endpoints
    hpoly hdim x.val y.val (l := x.val :: p.vertices.dropLast.map WallComplement.val)
    (List.cons_ne_nil _ _) (lt_min hε₁ hε₂)
  refine ⟨a, b, r, ?_, ?_⟩
  · intro u v s hs
    apply Eq.trans (hp s ?_) hprodP
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_left ε₁ ε₂)
    rwa [← hv, ← hs] at hnear
  · intro u v s hs
    apply Eq.trans (hq s ?_) hprodQ
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_right ε₁ ε₂)
    rwa [← hv, hvpq, ← hs] at hnear

end Quiver.Path
