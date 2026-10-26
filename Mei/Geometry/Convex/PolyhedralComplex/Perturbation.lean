/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.Perturbation

/-!
# Crossing words of perturbed paths

The signed crossing word of an admissible path through the walls of a finite polyhedral
complex is locally constant in the vertices of the path. For a segment, the perturbed
segment crosses the same walls in the same order (`Mei.Convex.WallComplement.AdmissibleSegment`
perturbation API), and its normal velocity has the same sign at each crossed wall, so every
signed letter is unchanged. For a polygonal path, it suffices that every vertex moves less
than a positive distance depending on the path; the endpoints may move as well.

Nearby paths admissible for any finite family of codimension-one polyhedra exist by
`Mei.Convex.AdmissiblePLPath.exists_forall₂_dist_lt`; the radius given here bounds how far
such a path may stray from the original one without changing the crossing word.
Coorientations are linear functionals whose kernels are the wall directions.
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Admissible segments with endpoints close to those of an admissible segment have its
crossing word. -/
theorem eventually_segmentCrossingWord_eq (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) (e : x ⟶ y) :
    ∀ᶠ q : V × V in 𝓝 (x.val, y.val),
      ∀ (x' y' : WallComplement (fun P : C.walls => (P : Set V))) (e' : x' ⟶ y'),
        x'.val = q.1 → y'.val = q.2 → C.segmentCrossingWord ν e' = C.segmentCrossingWord ν e := by
  have := h.finiteDimensional
  have hclosed (P : C.walls) : IsClosed (P : Set V) :=
    (C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.2)).isClosed
  have hdim (P : C.walls) := C.finrank_direction_add_one_of_mem_walls P.2
  -- The normal velocity keeps its nonzero sign at each crossed wall.
  filter_upwards [e.down.eventually_exists_mem_crossings_iff hclosed hdim,
    e.down.eventually_lt_iff_of_mem_crossings hdim,
    eventually_all.mpr (fun i => e.down.eventually_pos_iff_of_mem_crossings i (ν i) (hν i))]
    with ⟨a, b⟩ hwalls horder hsign
  rintro x' y' e' rfl rfl
  have hwalls := hwalls x' y' rfl rfl
  -- The wall lists of both segments are sorted by the original crossing order.
  let r : C.walls → C.walls → Prop := fun P Q => ∃ s t,
    (P, s) ∈ WallComplement.crossings x y ∧ (Q, t) ∈ WallComplement.crossings x y ∧ s < t
  have : Std.Irrefl r := ⟨fun P ⟨s, t, hs, ht, hst⟩ => hst.ne
    (e.down.subsingleton_crossing P ((WallComplement.mem_crossings x y P s).mp hs)
      ((WallComplement.mem_crossings x y P t).mp ht))⟩
  have : Std.Antisymm r := ⟨fun P Q ⟨s, t, hs, ht, hst⟩ ⟨t', s', ht', hs', hts⟩ => by
    obtain rfl := e.down.subsingleton_crossing P ((WallComplement.mem_crossings x y P s).mp hs)
      ((WallComplement.mem_crossings x y P s').mp hs')
    obtain rfl := e.down.subsingleton_crossing Q ((WallComplement.mem_crossings x y Q t).mp ht)
      ((WallComplement.mem_crossings x y Q t').mp ht')
    exact absurd (hst.trans hts) (lt_irrefl _)⟩
  have hpair : ((C.orderedCrossings e).map Prod.fst).Pairwise r :=
    List.pairwise_map.mpr ((C.pairwise_orderedCrossings e).imp_of_mem fun ha hb hab =>
      ⟨_, _, (C.mem_orderedCrossings e _).mp ha, (C.mem_orderedCrossings e _).mp hb, hab⟩)
  have hpair' : ((C.orderedCrossings e').map Prod.fst).Pairwise r := by
    refine List.pairwise_map.mpr ((C.pairwise_orderedCrossings e').imp_of_mem fun ha hb hab => ?_)
    have ha' := (C.mem_orderedCrossings e' _).mp ha
    have hb' := (C.mem_orderedCrossings e' _).mp hb
    obtain ⟨s, hs⟩ := (hwalls _).mp ⟨_, ha'⟩
    obtain ⟨t, ht⟩ := (hwalls _).mp ⟨_, hb'⟩
    exact ⟨s, t, hs, ht, (horder x' y' rfl rfl hs ht ha' hb').mp hab⟩
  have hmem (P : C.walls) : P ∈ (C.orderedCrossings e').map Prod.fst ↔
      P ∈ (C.orderedCrossings e).map Prod.fst := by
    simp only [List.mem_map, mem_orderedCrossings, Prod.exists, exists_and_right,
      exists_eq_right]
    exact hwalls P
  have hlist := hpair'.eq_of_mem_iff hpair hmem
  -- Each crossed wall contributes the same signed letter.
  have hword (x y : WallComplement (fun P : C.walls => (P : Set V))) (e : x ⟶ y) :
      C.segmentCrossingWord ν e =
        (((C.orderedCrossings e).map Prod.fst).reverse.map (C.crossingLetter ν x y)).prod := by
    simp only [segmentCrossingWord_def, List.map_reverse, List.map_map, Function.comp_def]
  rw [hword, hword, hlist]
  congr 1
  apply List.map_congr_left
  intro P hP
  have hP' := List.mem_reverse.mp hP
  simp only [List.mem_map, mem_orderedCrossings, Prod.exists, exists_and_right,
    exists_eq_right] at hP'
  simp only [crossingLetter_def, hsign P hP']

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- An admissible path has a positive radius such that every admissible path whose
vertices are, one by one, within that distance of its vertices has the same crossing word.
The endpoints may move. -/
theorem exists_pos_crossingWord_eq_of_forall₂_dist_lt (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (p : AdmissiblePLPath x y) :
    ∃ ε > 0, ∀ {x' y' : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath x' y'),
        List.Forall₂ (fun a b => dist a b < ε) (p.vertices.map WallComplement.val)
          (q.vertices.map WallComplement.val) → q.crossingWord ν = p.crossingWord ν := by
  have := h.finiteDimensional
  exact p.exists_pos_invariant_eq_of_forall₂_dist_lt
    (fun e => C.segmentCrossingWord ν e) (fun p => p.crossingWord ν)
    1 (fun word letter => letter * word) (fun _ => crossingWord_nil ν)
    (fun p e => crossingWord_cons p e ν) (C.eventually_segmentCrossingWord_eq ν hν)

end Quiver.Path
