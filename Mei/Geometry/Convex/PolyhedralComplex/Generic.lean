/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Relative
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Common regular points on walls

Every nonempty relatively open patch of a wall contains points outside the
singular supports of countably many finite polyhedral complexes. This is a
relative genericity statement: ambient generic points would miss the wall
itself. It permits testing local wall data simultaneously at every cutoff.

We use the inclusion of singular support in the codimension-two skeleton and
`AffineSubspace.exists_mem_open_avoid_of_finrank_lt`. No refinement relation
between the complexes is required, and lineality is allowed.
-/

public noncomputable section

open Set

namespace Mei.FinitePolyhedralComplex

variable {N V ι : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Countable ι]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Any open set meeting the intrinsic interior of a wall contains a point
on that interior regular for every complex in a countable family. -/
theorem exists_mem_wall_notMem_singularSupport (B : FinitePolyhedralComplex h)
    (P : B.walls) (C : ι → FinitePolyhedralComplex h)
    {U : Set V} (hU : IsOpen U)
    (hne : (U ∩ intrinsicInterior ℝ (P : Set V)).Nonempty) :
    ∃ x ∈ U ∩ intrinsicInterior ℝ (P : Set V),
      ∀ j, x ∉ Convex.singularSupport (fun Q : (C j).walls => (Q : Set V)) := by
  have := h.finiteDimensional
  let E : (Σ j, (C j).codimensionAtLeast 2 |>.cells) → AffineSubspace ℝ V :=
    fun q => affineSpan ℝ (q.2 : Set V)
  have hdim (q) : Module.finrank ℝ (E q).direction <
      Module.finrank ℝ (affineSpan ℝ (P : Set V)).direction := by
    have hP := B.finrank_direction_add_one_of_mem_walls P.property
    have hQ := ((C q.1).mem_codimensionAtLeast_cells 2 q.2).mp q.2.property
    dsimp only [E]
    omega
  obtain ⟨x, hx, havoid⟩ := (P : Set V).exists_mem_intrinsicInterior_avoid_of_finrank_lt
    E hdim hU hne
  refine ⟨x, hx, fun j hj => ?_⟩
  obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp
    ((C j).singularSupport_walls_subset_support_codimensionAtLeast hj)
  exact havoid ⟨j, ⟨Q, hQ⟩⟩ (subset_affineSpan ℝ Q hxQ)

/-- Every wall has an intrinsic interior point regular for a countable family
of complexes, regardless of how their subdivisions change. -/
theorem exists_mem_intrinsicInterior_wall_notMem_singularSupport
    (B : FinitePolyhedralComplex h) (P : B.walls)
    (C : ι → FinitePolyhedralComplex h) :
    ∃ x ∈ intrinsicInterior ℝ (P : Set V),
      ∀ j, x ∉ Convex.singularSupport (fun Q : (C j).walls => (Q : Set V)) := by
  have := h.finiteDimensional
  have hP := B.mem_cells_of_mem_walls P.property
  obtain ⟨x, ⟨-, hx⟩, hreg⟩ := B.exists_mem_wall_notMem_singularSupport P C isOpen_univ
    (by simpa using (B.nonempty _ hP).intrinsicInterior (B.isConvexPolyhedron hP).convex)
  exact ⟨x, hx, hreg⟩

end Mei.FinitePolyhedralComplex
