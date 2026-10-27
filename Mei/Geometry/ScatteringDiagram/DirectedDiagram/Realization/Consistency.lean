/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence

/-!
# Testing directed consistency on adapted complexes

Every finite-order loop product can be computed by a loop admissible for the
adapted complex, even if the original basepoint lies on an artificial wall.
Consequently a directed diagram is consistent at a cutoff exactly when its
finite adapted wall diagram is consistent. This allows consistency arguments
on finite polyhedral complexes to apply to all original indexed-wall paths.

The loop replacement combines
`AdmissiblePLPath.exists_loop_forall₂_dist_lt` with
`DirectedDiagram.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt`.
Stationary padding handles constant paths without changing their transport.
The product comparison is `DirectedDiagram.levelPathProduct_eq_adaptedDiagram`.
The moving-basepoint argument follows `DirectedDiagram.LevelEquivalent.consistent`;
no consistency, geometric joint relations, or commutativity of distinct wall
labels is assumed in the replacement construction.
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

/-- Every loop transport at a finite cutoff has a representative admissible for
the adapted complex. The basepoint may move off artificial walls, and the loop
remains closed. This includes the constant path and retains the original product,
rather than only its conjugacy class. -/
theorem exists_adapted_loop_levelPathProduct_eq (k : ℕ)
    {x : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x x) :
    ∃ (a : WallComplement (fun Q : (D.adaptedComplex k).walls => (Q : Set V)))
      (q : AdmissiblePLPath a a),
      D.levelPathProduct k ((D.adaptedPathPrefunctor k).mapPath q) =
        D.levelPathProduct k p := by
  let := h.finiteDimensional
  let C := D.adaptedComplex k
  obtain ⟨p', hvp, hprod⟩ := D.exists_vertices_eq_cons_levelPathProduct_eq k p
  obtain ⟨ε, hε, hstable⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p'
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [x.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  -- Perturb both occurrences of the basepoint to the same allowed point.
  obtain ⟨a, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt
    (fun Q : C.walls => C.isConvexPolyhedron (C.mem_cells_of_mem_walls Q.property))
    (fun Q : C.walls => C.finrank_direction_add_one_of_mem_walls Q.property)
    x.val (l := x.val :: p.vertices.dropLast.map WallComplement.val) hε
  refine ⟨a, q, (hstable ((D.adaptedPathPrefunctor k).mapPath q) ?_).trans hprod⟩
  simpa only [hv, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    D.adaptedPathPrefunctor_obj_val] using hq

/-- Testing only loops admissible for the adapted complex detects consistency
of the entire indexed diagram. In particular, basepoints on artificial adapted
walls do not require additional tests. -/
theorem levelConsistent_iff_adapted_loops (k : ℕ) :
    D.LevelConsistent k ↔
      ∀ (a : WallComplement (fun Q : (D.adaptedComplex k).walls => (Q : Set V)))
        (q : AdmissiblePLPath a a),
        D.levelPathProduct k ((D.adaptedPathPrefunctor k).mapPath q) = 1 := by
  rw [D.levelConsistent_iff_loops]
  constructor
  · intro hD a q
    exact hD _ _
  · intro hD x p
    obtain ⟨a, q, he⟩ := D.exists_adapted_loop_levelPathProduct_eq k p
    exact he.symm.trans (hD a q)

/-- A directed diagram is consistent at a cutoff exactly when the finite wall
diagram on its adapted complex is consistent. The equivalence holds for every
choice of coorientations and includes all original admissible paths. -/
theorem levelConsistent_iff_adaptedDiagram_consistent (k : ℕ)
    (ν : (D.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ Q, (ν Q).ker = (affineSpan ℝ (Q : Set V)).direction) :
    D.LevelConsistent k ↔ (D.adaptedDiagram k ν hν).Consistent := by
  rw [D.levelConsistent_iff_adapted_loops k,
    (D.adaptedDiagram k ν hν).consistent_iff_loops]
  simp only [D.levelPathProduct_eq_adaptedDiagram ν hν]

end Mei.DirectedDiagram
