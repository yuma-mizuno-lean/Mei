/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Transverse
public import Mei.Geometry.Convex.Polyhedron.GenericPath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Admissible polygonal paths through wall families

Vertices lie off every wall. Edges avoid singular support and are transverse
to each wall they meet. Admissible polygonal paths are Mathlib quiver paths
on these vertices: constant paths, concatenation and reversal use the existing
`Quiver.Path` operations and laws. Their continuous realizations concatenate
`Path.segment`s.

For a finite family, the crossing events (segment index, wall index and affine
parameter) form a finite set. Thus repeated visits and simultaneous coplanar
crossings are retained. For closed walls, every crossing lies in the relative
interior of its wall. In finite dimension, finite families of codimension-one
polyhedra admit such paths between any two allowed endpoints, with two edges
sufficing.
-/

public section

open Set
open scoped unitInterval

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vertex outside every member of a wall family. -/
@[ext]
structure WallComplement (W : ι → Set V) where
  /-- The ambient point. -/
  val : V
  /-- The point lies on no wall. -/
  not_mem : ∀ i, val ∉ W i

namespace WallComplement

variable {W : ι → Set V}

/-- An admissible segment avoids singular support and is transverse to each
wall it meets. Disjoint segments, including constant segments, need no rank condition. -/
structure AdmissibleSegment (x y : WallComplement W) : Prop where
  /-- A meeting segment has direction outside the wall direction. -/
  transverse : ∀ i, (∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ W i) →
    y.val - x.val ∉ (affineSpan ℝ (W i)).direction
  /-- All points of the segment avoid the actual singular support. -/
  regular : ∀ t ∈ Icc (0 : ℝ) 1,
    AffineMap.lineMap x.val y.val t ∉ singularSupport W

/-- Admissible segments are the edges of the quiver of allowed vertices. -/
instance : Quiver (WallComplement W) where
  Hom x y := PLift (AdmissibleSegment x y)

namespace AdmissibleSegment

variable {x y : WallComplement W}

/-- Reversing an admissible segment preserves its geometric conditions. -/
theorem symm (h : AdmissibleSegment x y) : AdmissibleSegment y x where
  transverse i hi := by
    obtain ⟨t, ht, hti⟩ := hi
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hd := h.transverse i
      ⟨1 - t, ht', by simpa only [AffineMap.lineMap_apply_one_sub] using hti⟩
    intro hh
    apply hd
    simpa only [neg_sub] using (affineSpan ℝ (W i)).direction.neg_mem hh
  regular t ht := by
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    simpa only [AffineMap.lineMap_apply_one_sub] using h.regular (1 - t) ht'

/-- An edge crosses a given wall at at most one affine parameter. -/
theorem subsingleton_crossing (h : AdmissibleSegment x y) (i : ι) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i}.Subsingleton := by
  intro s hs t ht
  exact (affineSpan ℝ (W i)).subsingleton_preimage_lineMap
    (h.transverse i ⟨s, hs.1, hs.2⟩)
    (subset_affineSpan ℝ (W i) hs.2) (subset_affineSpan ℝ (W i) ht.2)

/-- Every crossing is at a strictly interior parameter and in the relative
interior of its closed wall. -/
theorem crossing_mem_intrinsicInterior (h : AdmissibleSegment x y)
    {i : ι} (hclosed : IsClosed (W i)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hi : AffineMap.lineMap x.val y.val t ∈ W i) :
    t ∈ Ioo (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ intrinsicInterior ℝ (W i) := by
  have hzero : t ≠ 0 := by intro he; exact x.not_mem i (by simpa [he] using hi)
  have hone : t ≠ 1 := by intro he; exact y.not_mem i (by simpa [he] using hi)
  refine ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩, ?_⟩
  rw [← intrinsicClosure_sdiff_intrinsicFrontier,
    (hclosed.preimage continuous_subtype_val).intrinsicClosure]
  refine ⟨hi, ?_⟩
  intro hb
  exact h.regular t ht (mem_singularSupport.mpr (Or.inl ⟨i, hb⟩))

/-- The wall indices and affine crossing parameters of one segment. -/
def crossings (x y : WallComplement W) : Set (ι × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val p.2 ∈ W p.1}

/-- The characteristic membership test for segment crossings. -/
@[simp]
theorem mem_crossings (x y : WallComplement W) (i : ι) (t : ℝ) :
    (i, t) ∈ crossings x y ↔
      t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i := Iff.rfl

/-- A segment has finitely many indexed crossings for a finite wall family. -/
theorem finite_crossings [Finite ι] (h : AdmissibleSegment x y) : (crossings x y).Finite := by
  have heq : crossings x y = ⋃ i, Prod.mk i ''
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i} := by
    ext ⟨i, t⟩
    simp
  rw [heq]
  exact Set.finite_iUnion fun i => (h.subsingleton_crossing i).finite.image _

end AdmissibleSegment

/-- Reversal of segments makes the allowed-vertex quiver symmetric. -/
instance : Quiver.HasInvolutiveReverse (WallComplement W) where
  reverse' e := ⟨e.down.symm⟩
  inv' _ := PLift.ext (Subsingleton.elim _ _)

end WallComplement

/-- A finite chain of admissible affine segments between allowed endpoints.
The zero-edge path is the constant path. Concatenation and reversal are the
operations `Quiver.Path.comp` and `Quiver.Path.reverse`. -/
abbrev AdmissiblePLPath {W : ι → Set V} (x y : WallComplement W) := Quiver.Path x y

end Mei.Convex

namespace Quiver.Path

open Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Realize a finite admissible chain as a continuous path. -/
noncomputable def toPath : {y : WallComplement W} → AdmissiblePLPath x y → _root_.Path x.val y.val
  | _, .nil => Path.refl x.val
  | _, @Quiver.Path.cons _ _ _ u v p _ => (toPath p).trans (Path.segment u.val v.val)

/-- The realization of the zero-edge chain is constant. -/
@[simp]
theorem toPath_nil : toPath (Quiver.Path.nil : AdmissiblePLPath x x) = Path.refl x.val := (rfl)

/-- Appending an edge realizes as concatenation with its straight segment. -/
@[simp]
theorem toPath_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    toPath (p.cons e) = (toPath p).trans (Path.segment y.val z.val) := (rfl)

/-- Realizing concatenation agrees with continuous path concatenation up to
the usual homotopies of reparametrization. -/
theorem toPath_comp_homotopic (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (toPath (p.comp q)).Homotopic ((toPath p).trans (toPath q)) := by
  induction q with
  | nil => exact (Path.Homotopic.trans_refl _).symm
  | @cons u v q e ih =>
    exact (ih.hcomp (.refl (Path.segment u.val v.val))).trans
      (Path.Homotopic.trans_assoc _ _ _)

/-- Realizing reversal agrees, up to reparametrization homotopy, with reversal
of the continuous realization. -/
theorem toPath_reverse_homotopic (p : AdmissiblePLPath x y) :
    (toPath p.reverse).Homotopic (toPath p).symm := by
  induction p with
  | nil => exact .refl _
  | @cons u v p e ih =>
    have he : (toPath (Quiver.reverse e).toPath).Homotopic
        (Path.segment v.val u.val) := Path.Homotopic.refl_trans _
    have h := (toPath_comp_homotopic (Quiver.reverse e).toPath p.reverse).trans
      (he.hcomp ih)
    simpa only [Quiver.Path.reverse, toPath_cons, Path.trans_symm, Path.segment_symm] using h

/-- For closed walls, the continuous realization avoids singular support. -/
theorem toPath_not_mem_singularSupport (p : AdmissiblePLPath x y)
    (hclosed : ∀ i, IsClosed (W i)) (t : unitInterval) :
    toPath p t ∉ singularSupport W := by
  induction p generalizing t with
  | nil =>
    intro hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion W hclosed hs)
    exact x.not_mem i hi
  | @cons u v p e ih =>
    have hr : (toPath p).trans (Path.segment u.val v.val) t ∈
        Set.range (toPath p) ∪ Set.range (Path.segment u.val v.val) := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases hr with ⟨s, hs⟩ | ⟨s, hs⟩
    · simpa only [toPath_cons, ← hs] using ih s
    · simpa only [toPath_cons, ← hs, Path.segment_apply] using e.down.regular s.val s.property

/-- Indexed crossing events retain the edge number, wall index and affine
parameter. Distinct visits to the same geometric point remain distinct. -/
def crossingEvents : {y : WallComplement W} → AdmissiblePLPath x y → Set (ℕ × (ι × ℝ))
  | _, .nil => ∅
  | _, @Quiver.Path.cons _ _ _ u v p _ => crossingEvents p ∪
      Prod.mk p.length '' (WallComplement.AdmissibleSegment.crossings u v)

/-- A constant chain has no crossing events. -/
@[simp]
theorem crossingEvents_nil :
    crossingEvents (Quiver.Path.nil : AdmissiblePLPath x x) = ∅ := (rfl)

/-- Appending an edge adds exactly its indexed crossings. -/
@[simp]
theorem mem_crossingEvents_cons (p : AdmissiblePLPath x y) (e : y ⟶ z)
    (j : ℕ) (i : ι) (t : ℝ) :
    (j, i, t) ∈ crossingEvents (p.cons e) ↔
      (j, i, t) ∈ crossingEvents p ∨
        j = p.length ∧ (i, t) ∈ WallComplement.AdmissibleSegment.crossings y z := by
  simp [crossingEvents, eq_comm, and_assoc, and_left_comm, and_comm]

/-- Concatenation shifts the second path's edge indices by the first path's
length and retains all crossings of both paths. -/
@[simp]
theorem crossingEvents_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    crossingEvents (p.comp q) = crossingEvents p ∪
      (fun a : ℕ × (ι × ℝ) => (p.length + a.1, a.2)) '' crossingEvents q := by
  induction q with
  | nil => simp
  | @cons u v q e ih =>
    simp only [Quiver.Path.comp_cons, crossingEvents, ih, Set.image_union,
      Set.image_image, Quiver.Path.length_comp, Set.union_assoc]

/-- A finite wall family gives finitely many crossing events along every
admissible polygonal path, even with repeated visits or coincident walls. -/
theorem finite_crossingEvents [Finite ι] (p : AdmissiblePLPath x y) :
    (crossingEvents p).Finite := by
  induction p with
  | nil => exact Set.finite_empty
  | cons p e ih =>
    exact ih.union (e.down.finite_crossings.image (Prod.mk p.length))

end Quiver.Path

namespace Mei.Convex.AdmissiblePLPath

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}

/-- Allowed endpoints in a finite family of codimension-one polyhedra admit
an admissible chain with exactly two edges. -/
theorem exists_length_eq_two [FiniteDimensional ℝ V] [Finite ι]
    (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (x y : WallComplement W) : ∃ p : AdmissiblePLPath x y, p.length = 2 := by
  obtain ⟨v, _, hv, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
    W hpoly hdim x.not_mem y.not_mem isOpen_univ Set.univ_nonempty
  let z : WallComplement W := ⟨v, hv⟩
  have hxz : WallComplement.AdmissibleSegment x z :=
    ⟨fun i _ => (htrans i).1, fun t _ => (hreg t).1⟩
  have hyz : WallComplement.AdmissibleSegment y z :=
    ⟨fun i _ => (htrans i).2, fun t _ => (hreg t).2⟩
  exact ⟨((Quiver.Path.nil : AdmissiblePLPath x x).cons (PLift.up hxz)).cons
    (PLift.up hyz.symm), rfl⟩

end Mei.Convex.AdmissiblePLPath
