/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision
public import Mei.Geometry.Convex.Polyhedron.Path.Subdivision

/-!
# Subdivision into single-crossing segments

Every admissible polygonal path through the walls of a finite polyhedral complex
has a subdivision whose segments meet at most one wall. The endpoints are retained,
and every inserted vertex lies on its original segment and outside all walls.
Consequently the subdivision preserves the crossing word and permits local
single-crossing formulas to compute transport along arbitrary polygonal paths.

The construction specializes the indexed-wall event subdivision theorem
`WallComplement.exists_segment_subdivision_subsingleton_crossingTimes`.
For a complex, `FinitePolyhedralComplex.crossing_time_injective` turns a
single crossing time into a single wall crossing. No perturbation of the path
is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

/-- Subdivide an admissible segment, without moving its endpoints, so that each
new segment has at most one indexed wall crossing. -/
theorem exists_segment_subdivision_subsingleton_crossings
    {x y : WallComplement (fun P : C.walls => (P : Set V))} (e : x ⟶ y) :
    ∃ q : AdmissiblePLPath x y, e.toPath.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (WallComplement.crossings u v).Subsingleton) := by
  obtain ⟨q, hq, hsmall⟩ :=
    WallComplement.exists_segment_subdivision_subsingleton_crossingTimes e
  refine ⟨q, hq, ?_⟩
  clear hq e
  induction q with
  | nil => simp
  | @cons y z q f ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp] at hsmall ⊢
    refine ⟨ih hsmall.1, ?_⟩
    simp only [Quiver.Path.vertices_toPath, List.isChain_pair] at *
    intro a ha b hb
    exact congrArg Subtype.val (C.crossing_time_injective f
      (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (hsmall.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩))

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Every admissible polygonal path has a subdivision into segments meeting at
most one wall. This retains the path's geometry and its ordered crossing word. -/
theorem exists_subdivision_subsingleton_crossings (p : AdmissiblePLPath x y) :
    ∃ q : AdmissiblePLPath x y, p.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (WallComplement.crossings u v).Subsingleton) := by
  induction p with
  | nil => exact ⟨.nil, .refl _, by simp⟩
  | cons p e ih =>
    obtain ⟨q, hq, hsmall⟩ := ih
    obtain ⟨r, hr, hrsmall⟩ := C.exists_segment_subdivision_subsingleton_crossings e
    exact ⟨q.comp r, .comp hq hr,
      (isChain_vertices_comp _ _ _).mpr ⟨hsmall, hrsmall⟩⟩

end Quiver.Path
