/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Adapted
public import Mei.Geometry.Convex.PolyhedralComplex.Meridian
public import Mei.Geometry.Convex.Polyhedron.Path.Coarsening

/-!
# Directed meridians at adapted joints

Every conormally oriented joint of an adapted complex admits arbitrarily small
positive triangular meridians admissible for the original active directed wall
family. The filled triangle isolates the joint in the entire codimension-two
skeleton, misses its relative boundary and all other joints, and meets only
active supports containing the joint. Thus its directed path product is an
actual local loop product, including all coincident indexed contributions.
The vertices miss the supporting affine spans of all incident adapted wall
cells and active directed supports. This permits local facet Stokes formulas
to be applied to the same meridians used for directed transport.

The construction combines
`FinitePolyhedralComplex.exists_positive_isolating_joint_triangle` with
`DirectedDiagram.exists_mem_adaptedComplex_walls_subset` and
`WallComplement.wallCoverPrefunctor`. Equal codimensions identify each covering
cell's affine span with that of its directed support. No consistency assumption
is needed to construct these loops; lower-order consistency subsequently puts
their products in the central truncation kernel.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

private theorem adapted_wall_cover (k : ℕ) (j : D.active k) (x : V)
    (hx : x ∈ (D.wall j).support) :
    ∃ Q : (D.adaptedComplex k).walls, x ∈ (Q : Set V) ∧
      (Q : Set V) ⊆ (D.wall j).support ∧
      affineSpan ℝ (Q : Set V) = affineSpan ℝ (D.wall j).support := by
  let := h.finiteDimensional
  obtain ⟨Q, hQ, hxQ, hsub⟩ := D.exists_mem_adaptedComplex_walls_subset k j hx
  have hle := affineSpan_mono ℝ hsub
  have hdimQ := (D.adaptedComplex k).finrank_direction_add_one_of_mem_walls hQ
  have hdimW := (D.wall j).finrank_direction_add_one
  have hdir := Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    (by omega : Module.finrank ℝ (affineSpan ℝ Q).direction =
      Module.finrank ℝ (affineSpan ℝ (D.wall j).support).direction)
  exact ⟨⟨Q, hQ⟩, hxQ, hsub,
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ⟨x, subset_affineSpan ℝ Q hxQ⟩ hle⟩

/-- An oriented adapted joint has arbitrarily small positive triangular loops
admissible for the active directed supports. Their filled triangles isolate the
joint in the adapted skeleton and meet only active supports containing it.
The vertex formula specifies the actual path used by `levelPathProduct`.
Vertices also avoid the affine spans of incident adapted cells and active
supports, including coincident supports. -/
theorem exists_positive_isolating_joint_triangle {k : ℕ} {J : Set V}
    (hJ : J ∈ (D.adaptedComplex k).joints) {p : V}
    (hp : p ∈ intrinsicInterior ℝ J)
    (o : Module.Ray ℝ (V [⋀^Fin 2]→ₗ[ℝ] ℝ))
    (ho : o.IsConormal (affineSpan ℝ J).direction) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Affine.Triangle ℝ V)
      (x : WallComplement (fun j : D.active k => (D.wall j).support))
      (γ : AdmissiblePLPath x x),
      0 < o.someVector (fun j : Fin 2 => s.points j.succ - s.points 0) ∧
      s.centroid = p ∧
      γ.vertices.map WallComplement.val = [s.points 0, s.points 1, s.points 2, s.points 0] ∧
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) ∧
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε ∧
      convexHull ℝ (range s.points) ∩
        ((D.adaptedComplex k).codimensionAtLeast 2).support = {p} ∧
      Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ J) ∧
      (∀ Q ∈ (D.adaptedComplex k).joints, Q ≠ J →
        Disjoint (convexHull ℝ (range s.points)) Q) ∧
      (∀ j : D.active k,
        (convexHull ℝ (range s.points) ∩ (D.wall j).support).Nonempty →
          J ⊆ (D.wall j).support) ∧
      (∀ m Q, Q ∈ (D.adaptedComplex k).walls → J ⊆ Q →
        s.points m ∉ affineSpan ℝ Q) ∧
      ∀ m (j : D.active k), J ⊆ (D.wall j).support →
        s.points m ∉ affineSpan ℝ (D.wall j).support := by
  obtain ⟨s, x, γ, hpos, hcenter, hvertices, hcompl, hball, hskeleton,
      hfrontier, hother, hcells, hspan⟩ :=
    (D.adaptedComplex k).exists_positive_isolating_joint_triangle hJ hp o ho hε
  let F := WallComplement.wallCoverPrefunctor
    (fun j : D.active k => (D.wall j).isConvexPolyhedron.isClosed) (D.adapted_wall_cover k)
  refine ⟨s, F.obj x, F.mapPath γ, hpos, hcenter, ?_, hcompl, hball,
    hskeleton, hfrontier, hother, ?_, hspan, ?_⟩
  · simpa only [F, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      WallComplement.wallCoverPrefunctor_obj_val] using hvertices
  · rintro j ⟨y, hy, hyj⟩
    obtain ⟨Q, hQ, hyQ, hsub⟩ := D.exists_mem_adaptedComplex_walls_subset k j hyj
    exact (hcells Q ((D.adaptedComplex k).mem_cells_of_mem_walls hQ) ⟨y, hy, hyQ⟩).trans hsub
  · intro m j hJj
    obtain ⟨Q, hpQ, -, hQspan⟩ := D.adapted_wall_cover k j p (hJj (intrinsicInterior_subset hp))
    have hJQ := (D.adaptedComplex k).subset_of_mem_intrinsicInterior
      (((D.adaptedComplex k).mem_cellsOfCodimension 2 J).mp hJ).1
      ((D.adaptedComplex k).mem_cells_of_mem_walls Q.property) hp hpQ
    rw [← hQspan]
    exact hspan m Q Q.property hJQ

end Mei.DirectedDiagram
