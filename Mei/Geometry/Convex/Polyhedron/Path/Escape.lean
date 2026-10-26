/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Sum
public import Mei.Geometry.Convex.Polyhedron.Path.Perturbation
public import Mei.Geometry.Convex.Polyhedron.Escape

/-!
# Crossing sums of walls escaping in a common direction

Let a finite family of closed codimension-one polyhedral walls carry coefficients in an
abelian group. Suppose a vector `v` is parallel to every wall with nonzero coefficient,
and lies outside its recession cone. If the signed crossing sum vanishes around every
admissible loop at a point, then it vanishes along every admissible path from that
point. Walls with zero coefficient may have arbitrary supports and positions.

The geometric input is that any two allowed points are joined by an admissible path
meeting no wall, when every wall escapes in the direction `v`: leave each endpoint for a
nearby point off the supporting hyperplanes, move parallel to the walls along `v`, and
cross over along a far translate of the segment between them, which misses every wall by
`Mei.Convex.eventually_forall_notMem_of_notMem_recessionCone`. For the
crossing sums, such a return path through the walls with nonzero coefficient is moved
into general position for the whole family by
`Quiver.Path.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt`, and closes every
path into a loop.

This is the rectangle argument showing that a consistent, abelian, outgoing part of a
scattering diagram vanishes, in the uniqueness part of the proof of Theorem 2.6 in
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5).
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.Convex.AdmissiblePLPath

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Finite ι] {W : ι → Set V}

/-- If every wall is a polyhedron in a proper affine subspace parallel to `v`, with `v`
outside its recession cone, then any two allowed points are joined by an admissible path
with at least one interior vertex and no crossings. -/
theorem exists_signedCrossingEvents_eq_nil_of_notMem_recessionCone
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j)) (hA : ∀ j, affineSpan ℝ (W j) ≠ ⊤)
    {v : V} (hpar : ∀ j, v ∈ (affineSpan ℝ (W j)).direction)
    (hrec : ∀ j, v ∉ recessionCone (W j)) (x y : WallComplement W) :
    ∃ l : List V, l ≠ [] ∧ ∃ p : AdmissiblePLPath x y,
      p.vertices.map WallComplement.val = x.val :: (l ++ [y.val]) ∧
        ∀ ν : ι → V →ₗ[ℝ] ℝ, p.signedCrossingEvents ν = [] := by
  have hclosed : ∀ j, IsClosed (W j) := fun j => (hpoly j).isClosed
  -- A line parallel to `v` through a point off the affine spans misses every wall.
  have hline (u : V) (hu : ∀ j, u ∉ affineSpan ℝ (W j)) (r : ℝ) (j : ι) : u + r • v ∉ W j := by
    intro hmem
    apply hu j
    simpa [vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction
      ((affineSpan ℝ (W j)).direction.neg_mem ((affineSpan ℝ (W j)).direction.smul_mem r
        (hpar j))) (subset_affineSpan ℝ _ hmem)
  -- Leave each endpoint for a nearby point off the affine spans, inside a ball missing walls.
  have hball (z : WallComplement W) : ∃ δ > 0, ∀ u ∈ Metric.ball z.val δ, ∀ j, u ∉ W j :=
    Metric.eventually_nhds_iff_ball.mp
      (eventually_all.mpr fun j => (hclosed j).isOpen_compl.mem_nhds (z.notMem j))
  obtain ⟨δx, hδx, hx⟩ := hball x
  obtain ⟨δy, hδy, hy⟩ := hball y
  obtain ⟨x', hx'δ, hx'A⟩ := AffineSubspace.exists_dist_lt_genericLocus _ hA x.val hδx
  obtain ⟨y', hy'δ, hy'A⟩ := AffineSubspace.exists_dist_lt_genericLocus _ hA y.val hδy
  -- Far translates of the segment from `x'` to `y'` miss every wall.
  obtain ⟨t, ht⟩ := (eventually_all.mpr fun j =>
    eventually_forall_notMem_of_notMem_recessionCone (hpoly j) (hrec j)
      ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image
        (AffineMap.lineMap_continuous (p := x') (q := y')))).exists
  let X₁ : WallComplement W := ⟨x', hx x' hx'δ⟩
  let Y₁ : WallComplement W := ⟨y', hy y' hy'δ⟩
  let X₂ : WallComplement W := ⟨x' + t • v, hline x' hx'A t⟩
  let Y₂ : WallComplement W := ⟨y' + t • v, hline y' hy'A t⟩
  have hempty {a b : WallComplement W}
      (hab : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ j, AffineMap.lineMap a.val b.val τ ∉ W j) :
      crossings a b = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun ⟨j, τ⟩ hτ =>
      hab τ ((mem_crossings _ _ _ _).mp hτ).1 j ((mem_crossings _ _ _ _).mp hτ).2
  have hnear {z : WallComplement W} {δ : ℝ} {z' : V}
      (hz : ∀ u ∈ Metric.ball z.val δ, ∀ j, u ∉ W j) (hz' : z' ∈ Metric.ball z.val δ)
      (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) : ∀ j, AffineMap.lineMap z.val z' τ ∉ W j :=
    hz _ ((convex_ball _ _).lineMap_mem (Metric.mem_ball_self (Metric.pos_of_mem_ball hz'))
      hz' hτ)
  have hside (u : V) (hu : ∀ j, u ∉ affineSpan ℝ (W j)) (τ : ℝ) (j : ι) :
      AffineMap.lineMap u (u + t • v) τ ∉ W j := by
    simpa [AffineMap.lineMap_apply, smul_smul, add_comm] using hline u hu (τ * t) j
  -- The path `x → X₁ → X₂ → Y₂ → Y₁ → y` meets no wall.
  have c₁ : crossings x X₁ = ∅ := hempty fun τ hτ => hnear hx hx'δ τ hτ
  have c₂ : crossings X₁ X₂ = ∅ := hempty fun τ _ => hside x' hx'A τ
  have c₃ : crossings X₂ Y₂ = ∅ := hempty fun τ hτ j => by
    have he : AffineMap.lineMap (x' + t • v) (y' + t • v) τ =
        AffineMap.lineMap x' y' τ + t • v := by
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module',
        add_sub_add_right_eq_sub, add_assoc]
    simpa only [X₂, Y₂, he] using ht j _ (mem_image_of_mem _ hτ)
  have c₄ : crossings Y₂ Y₁ = ∅ := hempty fun τ _ => by
    rw [← AffineMap.lineMap_apply_one_sub]
    exact hside y' hy'A (1 - τ)
  have c₅ : crossings Y₁ y = ∅ := hempty fun τ hτ => by
    rw [← AffineMap.lineMap_apply_one_sub]
    exact hnear hy hy'δ (1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  let e₁ : x ⟶ X₁ := ⟨.of_crossings_eq_empty hclosed c₁⟩
  let e₂ : X₁ ⟶ X₂ := ⟨.of_crossings_eq_empty hclosed c₂⟩
  let e₃ : X₂ ⟶ Y₂ := ⟨.of_crossings_eq_empty hclosed c₃⟩
  let e₄ : Y₂ ⟶ Y₁ := ⟨.of_crossings_eq_empty hclosed c₄⟩
  let e₅ : Y₁ ⟶ y := ⟨.of_crossings_eq_empty hclosed c₅⟩
  refine ⟨[x', x' + t • v, y' + t • v, y'], by simp,
    ((((e₁.toPath.cons e₂).cons e₃).cons e₄).cons e₅), by simp [X₁, X₂, Y₁, Y₂], fun ν => ?_⟩
  simp only [Quiver.Path.signedCrossingEvents_cons, Quiver.Hom.toPath,
    Quiver.Path.signedCrossingEvents_nil, (segmentCrossingEvents_eq_nil_iff ν _).mpr c₁,
    (segmentCrossingEvents_eq_nil_iff ν _).mpr c₂, (segmentCrossingEvents_eq_nil_iff ν _).mpr c₃,
    (segmentCrossingEvents_eq_nil_iff ν _).mpr c₄, (segmentCrossingEvents_eq_nil_iff ν _).mpr c₅,
    List.append_nil]

end Mei.Convex.AdmissiblePLPath

namespace Quiver.Path

variable {V ι E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Finite ι] [AddCommGroup E] {W : ι → Set V}

/-- If every wall with nonzero coefficient has a compatible normal, is parallel to `v`,
and has `v` outside its recession cone, then a crossing sum vanishing around all admissible
loops at `x` vanishes along all admissible paths from `x`. -/
theorem wallCrossingSum_eq_zero_of_notMem_recessionCone
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 = Module.finrank ℝ V)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → LinearMap.ker (ν j) = (affineSpan ℝ (W j)).direction)
    {v : V} (hpar : ∀ j, c j ≠ 0 → ν j v = 0)
    (hrec : ∀ j, c j ≠ 0 → v ∉ recessionCone (W j)) {x y : WallComplement W}
    (hloop : ∀ q : AdmissiblePLPath x x, q.wallCrossingSum ν c = 0)
    (p : AdmissiblePLPath x y) :
    p.wallCrossingSum ν c = 0 := by
  classical
  -- Keep only the walls with nonzero coefficients.
  let S := {j // c j ≠ 0}
  have hc : ∀ j, j ∉ range (Subtype.val : S → ι) → c j = 0 := fun j hj => by
    by_contra hcj
    exact hj ⟨⟨j, hcj⟩, rfl⟩
  -- Among those walls, return from `y` to `x` without crossing any.
  have hpar' (s : S) : v ∈ (affineSpan ℝ (W s.1)).direction := by
    rw [← hν s.1 s.2, LinearMap.mem_ker]
    exact hpar s.1 s.2
  obtain ⟨l, hl, r', hr'v, hr'e⟩ :=
    AdmissiblePLPath.exists_signedCrossingEvents_eq_nil_of_notMem_recessionCone
      (W := W ∘ (Subtype.val : S → ι)) (fun s => hpoly s.1)
      (fun s => (affineSpan ℝ (W s.1)).ne_top_of_finrank_direction_add_one_eq (hdim s.1))
      hpar' (fun s => hrec s.1 s.2)
      ((restrictPrefunctor W (Subtype.val : S → ι)).obj y)
      ((restrictPrefunctor W (Subtype.val : S → ι)).obj x)
  -- Move the return path into general position for all walls, keeping those crossings.
  have hclosed' : ∀ s : S, IsClosed ((W ∘ (Subtype.val : S → ι)) s) :=
    fun s => (hpoly s.1).isClosed
  have hdim' : ∀ s : S, Module.finrank ℝ (affineSpan ℝ ((W ∘ (Subtype.val : S → ι)) s)).direction
      + 1 = Module.finrank ℝ V := fun s => hdim s.1
  have hν' : ∀ s : S, LinearMap.ker ((ν ∘ (Subtype.val : S → ι)) s) =
      (affineSpan ℝ ((W ∘ (Subtype.val : S → ι)) s)).direction := fun s => hν s.1 s.2
  obtain ⟨ε, hε, hev⟩ := r'.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt
    hclosed' hdim' (ν ∘ Subtype.val) hν'
  obtain ⟨r, hr⟩ := AdmissiblePLPath.exists_forall₂_dist_lt hpoly hdim hl hε y x
  have hq := hev ((restrictPrefunctor W (Subtype.val : S → ι)).mapPath r)
    (by rwa [vertices_restrictPrefunctor, hr'v])
  have hr0 : r.wallCrossingSum ν c = 0 := by
    rw [← wallCrossingSum_restrict ν c Subtype.val Subtype.val_injective hc r,
      wallCrossingSum_def, hq, hr'e, List.map_nil, List.sum_nil]
  have hloop' := hloop (p.comp r)
  rwa [wallCrossingSum_comp, hr0, add_zero] at hloop'

end Quiver.Path
