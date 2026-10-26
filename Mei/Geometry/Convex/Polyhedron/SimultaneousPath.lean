/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Segment
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Simultaneously admissible polygonal paths

Admissibility of a segment through a finite closed wall family is open in its
endpoints. For fixed allowed endpoints, the intermediate vertices giving two
admissible segments form an open dense set when the walls are codimension-one
polyhedra. Baire's theorem then gives a dense Gδ set of vertices working for
countably many finite families simultaneously, even when their unions are not
locally finite. All endpoints remain fixed, and the same two-edge geometric
path works at every level.

This develops the endpoint topology of `WallComplement.AdmissibleSegment`,
using the finite-family construction
`Mei.Convex.exists_mem_open_two_transverse_lineMaps` and Mathlib's
`dense_iInter_of_isOpen`. No preservation of prescribed crossing words is asserted.
-/

public section

open Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Endpoint pairs defining admissible segments: both endpoints miss the walls,
meeting segments are transverse, and the segment misses singular support. -/
def admissiblePairs (W : ι → Set V) : Set (V × V) :=
  {p | (∀ i, p.1 ∉ W i) ∧ (∀ i, p.2 ∉ W i) ∧
    (∀ i, (∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∈ W i) →
      p.2 - p.1 ∉ (affineSpan ℝ (W i)).direction) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∉ singularSupport W}

/-- On allowed vertices, the endpoint-pair condition is precisely the existing
admissible-segment predicate. -/
@[simp]
theorem mem_admissiblePairs_iff {W : ι → Set V} (x y : WallComplement W) :
    (x.val, y.val) ∈ admissiblePairs W ↔ WallComplement.AdmissibleSegment x y := by
  constructor
  · rintro ⟨_, _, ht, hr⟩
    exact ⟨ht, hr⟩
  · intro h
    exact ⟨x.notMem, y.notMem, h.transverse, h.regular⟩

/-- The raw endpoint-pair condition supplies allowed vertices and an admissible
segment between them. -/
theorem mem_admissiblePairs {W : ι → Set V} {x y : V} :
    (x, y) ∈ admissiblePairs W ↔
      ∃ (hx : ∀ i, x ∉ W i) (hy : ∀ i, y ∉ W i),
        WallComplement.AdmissibleSegment ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · rintro ⟨hx, hy, ht, hr⟩
    exact ⟨hx, hy, ht, hr⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, h.transverse, h.regular⟩

/-- Segment admissibility is open in both endpoints for finite closed wall
families. Disjoint segments need no transversality assumption. -/
theorem isOpen_admissiblePairs [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hclosed : ∀ i, IsClosed (W i)) :
    IsOpen (admissiblePairs W) := by
  have hvertices : IsOpen {p : V × V | (∀ i, p.1 ∉ W i) ∧ ∀ i, p.2 ∉ W i} :=
    by
      convert (isOpen_iInter_of_finite fun i =>
        (hclosed i).isOpen_compl.preimage continuous_fst).inter
          (isOpen_iInter_of_finite fun i =>
            (hclosed i).isOpen_compl.preimage continuous_snd) using 1
      ext p
      simp
  have htrans : IsOpen {p : V × V | ∀ i,
      (∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∈ W i) →
        p.2 - p.1 ∉ (affineSpan ℝ (W i)).direction} := by
    have hopen := isOpen_iInter_of_finite fun i =>
      ((hclosed i).isOpen_setOf_lineMap_notMem).union
        (((affineSpan ℝ (W i)).direction.closed_of_finiteDimensional).isOpen_compl.preimage
          (continuous_snd.sub continuous_fst))
    convert hopen using 1
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_preimage, mem_compl_iff]
    constructor
    · intro h i
      by_cases ht : ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∈ W i
      · exact Or.inr (h i ht)
      · exact Or.inl (by simpa only [not_exists, not_and] using ht)
    · intro h i ⟨t, ht, hmem⟩
      exact (h i).elim (fun ha => False.elim (ha t ht hmem)) id
  simpa only [admissiblePairs, ofPred_and, inter_assoc] using
    hvertices.inter (htrans.inter
      ((isClosed_singularSupport W hclosed).isOpen_setOf_lineMap_notMem))

/-- Admissibility of the two segments through a free vertex is open in that
vertex for finite closed wall families. -/
theorem isOpen_setOf_admissiblePairs [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hclosed : ∀ i, IsClosed (W i)) (x y : V) :
    IsOpen {z | (x, z) ∈ admissiblePairs W ∧ (z, y) ∈ admissiblePairs W} :=
  ((isOpen_admissiblePairs W hclosed).preimage
    (continuous_const.prodMk continuous_id)).inter
  ((isOpen_admissiblePairs W hclosed).preimage
    (continuous_id.prodMk continuous_const))

/-- Two segments through an intermediate vertex are simultaneously admissible
for a finite polyhedral wall family on a dense set of vertices. -/
theorem dense_setOf_admissiblePairs [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    {x y : V} (hx : ∀ i, x ∉ W i) (hy : ∀ i, y ∉ W i) :
    Dense {z | (x, z) ∈ admissiblePairs W ∧ (z, y) ∈ admissiblePairs W} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨z, hzU, hz, ht, hr⟩ :=
    exists_mem_open_two_transverse_lineMaps W hpoly hdim hx hy hU hne
  have hxz : WallComplement.AdmissibleSegment (⟨x, hx⟩ : WallComplement W) ⟨z, hz⟩ :=
    ⟨fun i _ => (ht i).1, fun t _ => (hr t).1⟩
  have hyz : WallComplement.AdmissibleSegment (⟨y, hy⟩ : WallComplement W) ⟨z, hz⟩ :=
    ⟨fun i _ => (ht i).2, fun t _ => (hr t).2⟩
  exact ⟨z, hzU, ⟨mem_admissiblePairs_iff _ _ |>.mpr hxz,
    mem_admissiblePairs_iff _ _ |>.mpr hyz.symm⟩⟩

section Simultaneous

variable [FiniteDimensional ℝ V] {J : Type*} {I : J → Type*}
  [∀ j, Finite (I j)] (W : ∀ j, I j → Set V)

/-- For any countable collection of finite closed wall families, the common
admissible intermediate-vertex locus is a Gδ set. -/
theorem isGδ_setOf_forall_admissiblePairs [Countable J]
    (hclosed : ∀ j i, IsClosed (W j i)) (x y : V) :
    IsGδ {z | ∀ j, (x, z) ∈ admissiblePairs (W j) ∧ (z, y) ∈ admissiblePairs (W j)} := by
  simpa only [ofPred_forall] using IsGδ.iInter_of_isOpen
    (fun j => isOpen_setOf_admissiblePairs (W j) (hclosed j) x y)

/-- With endpoints off every wall, countably many finite codimension-one
polyhedral families admit a dense common set of admissible intermediate vertices. -/
theorem dense_setOf_forall_admissiblePairs [Countable J]
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    {x y : V} (hx : ∀ j i, x ∉ W j i) (hy : ∀ j i, y ∉ W j i) :
    Dense {z | ∀ j, (x, z) ∈ admissiblePairs (W j) ∧ (z, y) ∈ admissiblePairs (W j)} := by
  simpa only [ofPred_forall] using dense_iInter_of_isOpen
    (fun j => isOpen_setOf_admissiblePairs (W j) (fun i => (hpoly j i).isClosed) x y)
    (fun j => dense_setOf_admissiblePairs (W j) (hpoly j) (hdim j) (hx j) (hy j))

/-- There is one geometric two-edge polygonal path admissible for every family,
with its free vertex in any prescribed nonempty open set. Its quiver realizations
at the different levels are exactly the same continuous path. -/
theorem exists_mem_open_simultaneous_paths [Countable J]
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    {x y : V} (hx : ∀ j i, x ∉ W j i) (hy : ∀ j i, y ∉ W j i)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, ∀ j,
      ∃ p : AdmissiblePLPath (⟨x, hx j⟩ : WallComplement (W j)) ⟨y, hy j⟩,
        p.length = 2 ∧ p.toContinuousPath =
          ((Path.refl x).trans (Path.segment x z)).trans (Path.segment z y) := by
  obtain ⟨z, hzU, hz⟩ :=
    (dense_setOf_forall_admissiblePairs W hpoly hdim hx hy).inter_open_nonempty U hU hne
  refine ⟨z, hzU, ?_⟩
  intro j
  obtain ⟨_, hzj, hxz⟩ := mem_admissiblePairs.mp (hz j).1
  obtain ⟨_, _, hzy⟩ := mem_admissiblePairs.mp (hz j).2
  exact ⟨((Quiver.Path.nil : AdmissiblePLPath (⟨x, hx j⟩ : WallComplement (W j))
    ⟨x, hx j⟩).cons (PLift.up hxz)).cons (PLift.up hzy), rfl, by simp⟩

end Simultaneous

end Mei.Convex
