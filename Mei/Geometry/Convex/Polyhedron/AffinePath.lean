/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Affine transport of admissible polygonal paths

A continuous affine equivalence sends an admissible segment to an admissible
segment for the image wall family. The resulting quiver prefunctor transports
polygonal paths using Mathlib's `Prefunctor.mapPath`. Wall indices, affine
crossing parameters and edge indices are retained, including repeated visits
and simultaneous crossings. No finiteness, closedness, codimension or lattice
hypothesis on the wall family is needed.

The construction uses Mathlib's affine-span transport and
`ContinuousAffineEquiv.intrinsicFrontier_image` to transport singular support.
It provides the geometric part of coordinate transport for wall crossings.

`AffineEquiv.imagePrefunctor` additionally allows a bijective change of wall
indices in finite dimension. It reuses the continuous transport of segments;
the complex specialization uses it to transport signed crossing words.
-/

public section

open Set

namespace Mei.Convex.WallComplement

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- Send an allowed vertex to the complement of the image wall family.
This abbreviation keeps the endpoints of transported continuous paths reducible. -/
abbrev map (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    WallComplement (fun i => e '' W i) where
  val := e x.val
  notMem i := by simpa only [e.injective.mem_set_image] using x.notMem i

@[simp]
theorem map_val (e : V ≃ᴬ[ℝ] U) (x : WallComplement W) :
    (x.map e).val = e x.val := (rfl)

/-- Coordinate transport preserves the entire indexed crossing set, at the same parameters. -/
@[simp]
theorem crossings_map (e : V ≃ᴬ[ℝ] U) (x y : WallComplement W) :
    crossings (x.map e) (y.map e) = crossings x y := by
  ext ⟨i, t⟩
  have hline : e (AffineMap.lineMap x.val y.val t) =
      AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
  simp only [mem_crossings, ← hline, e.injective.mem_set_image]

/-- Affine coordinate changes preserve segment transversality and singular-support avoidance. -/
theorem AdmissibleSegment.map {x y : WallComplement W}
    (a : AdmissibleSegment x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissibleSegment (x.map e) (y.map e) where
  transverse i hi := by
    obtain ⟨t, ht, hi⟩ := hi
    have hmeet := (mem_crossings (x.map e) (y.map e) i t).mpr ⟨ht, hi⟩
    rw [crossings_map, mem_crossings] at hmeet
    have htrans := a.transverse i ⟨t, hmeet⟩
    -- Convert the equivalence coercion to the affine-map coercion used by span transport.
    have hcoe : (e.toAffineEquiv.toAffineMap : V → U) = e := by rfl
    rw [map_val, map_val, ← hcoe, ← AffineSubspace.map_span e.toAffineEquiv.toAffineMap,
      AffineSubspace.map_direction]
    have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
      e.toAffineEquiv.toAffineMap.linear_apply_vsub _ _
    rw [hcoe, ← hv]
    exact fun hh => htrans (by simpa only [AffineEquiv.linear_toAffineMap,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hh)
  regular t ht := by
    have hline : e (AffineMap.lineMap x.val y.val t) =
        AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
    simpa only [map_val, ← hline, singularSupport_image, e.injective.mem_set_image]
      using a.regular t ht

end Mei.Convex.WallComplement

namespace ContinuousAffineEquiv

open Mei.Convex

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- The quiver prefunctor that sends vertices and actual segments to their affine images.
Its object map is reducible so transported edges have the expected endpoints. -/
abbrev wallComplementPrefunctor (e : V ≃ᴬ[ℝ] U) :
    WallComplement W ⥤q WallComplement (fun i => e '' W i) where
  obj x := x.map e
  map a := ⟨a.down.map e⟩

@[simp]
theorem wallComplementPrefunctor_obj (e : V ≃ᴬ[ℝ] U) (x : WallComplement W) :
    (e.wallComplementPrefunctor).obj x = x.map e := (rfl)

/-- Affine transport preserves reversal of segments. -/
instance (e : V ≃ᴬ[ℝ] U) : (e.wallComplementPrefunctor (W := W)).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

end ContinuousAffineEquiv

namespace Quiver.Path

open Mei.Convex

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Transport the actual segments of an admissible polygonal path to an image wall family. -/
def affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissiblePLPath (x.map e) (y.map e) :=
  e.wallComplementPrefunctor.mapPath p

/-- Constant paths remain constant after transport. -/
@[simp]
theorem affineMap_nil (e : V ≃ᴬ[ℝ] U) :
    (nil : AdmissiblePLPath x x).affineMap e = nil := (rfl)

/-- Transport acts on each actual segment in a chain. -/
@[simp]
theorem affineMap_cons (p : AdmissiblePLPath x y) (a : y ⟶ z) (e : V ≃ᴬ[ℝ] U) :
    (p.cons a).affineMap e =
      (p.affineMap e).cons (e.wallComplementPrefunctor.map a) := (rfl)

/-- Affine transport commutes with path concatenation. -/
@[simp]
theorem affineMap_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (e : V ≃ᴬ[ℝ] U) :
    (p.comp q).affineMap e = (p.affineMap e).comp (q.affineMap e) :=
  Prefunctor.mapPath_comp _ _ _

/-- Transport retains the number of segments. -/
@[simp]
theorem length_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simp only [affineMap_cons, length_cons, ih]

/-- Reversing the transported chain is the transport of the reversed chain. -/
@[simp]
theorem affineMap_reverse (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    p.reverse.affineMap e = (p.affineMap e).reverse := by
  induction p with
  | nil => rfl
  | cons p a ih =>
    simp only [reverse, affineMap_comp, Quiver.Hom.toPath, affineMap_cons,
      affineMap_nil, ih]
    congr 2

/-- Every crossing event retains its edge index, wall index and affine parameter. -/
@[simp]
theorem crossingEvents_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).crossingEvents = p.crossingEvents := by
  induction p with
  | nil => simp
  | cons p a ih =>
    ext ⟨j, i, t⟩
    simp only [affineMap_cons, mem_crossingEvents_cons, ih, length_affineMap,
      WallComplement.crossings_map]

/-- The continuous realization of a transported chain is the image of its realization. -/
@[simp]
theorem toContinuousPath_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).toContinuousPath = p.toContinuousPath.map e.continuous := by
  induction p with
  | nil => ext t; simp [Path.map_coe]
  | @cons y z p a ih =>
    rw [affineMap_cons, toContinuousPath_cons, toContinuousPath_cons, Path.map_trans, ih]
    congr 1
    ext t
    exact (e.toAffineEquiv.apply_lineMap y.val z.val t).symm

end Quiver.Path

open Mei.Convex

namespace AffineEquiv

variable {V V' ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V]
  (e : V ≃ᵃ[ℝ] V') (f : ι ≃ κ) (W : ι → Set V) (W' : κ → Set V')
  (hW : ∀ j, W' (f j) = e '' W j)

/-- Transport allowed vertices and their actual admissible affine segments. -/
def imagePrefunctor : WallComplement W ⥤q WallComplement W' where
  obj x := ⟨e x.val, by
    intro j hj
    obtain ⟨j, rfl⟩ := f.surjective j
    rw [hW j] at hj
    exact x.notMem j (e.injective.mem_set_image.mp hj)⟩
  map {x y} a := ⟨{
    transverse j hj := by
      obtain ⟨j, rfl⟩ := f.surjective j
      have ha := a.down.map (e.toContinuousAffineEquiv)
      have htrans := ha.transverse j
      simp only [coe_toContinuousAffineEquiv] at htrans
      rw [hW j]
      exact htrans (by simpa only [hW j] using hj)
    regular t ht := by
      rw [← e.apply_lineMap, e.mem_singularSupport_image_iff f W W' hW]
      exact a.down.regular t ht }⟩

/-- Transport sends a vertex to its affine image. -/
@[simp]
theorem imagePrefunctor_obj_val (x : WallComplement W) :
    ((imagePrefunctor e f W W' hW).obj x).val = e x.val := (rfl)

/-- Affine transport retains each indexed crossing parameter. -/
@[simp high]
theorem mem_crossings_image (x y : WallComplement W) (j : ι) (t : ℝ) :
    (f j, t) ∈ WallComplement.crossings ((imagePrefunctor e f W W' hW).obj x)
        ((imagePrefunctor e f W W' hW).obj y) ↔ (j, t) ∈ WallComplement.crossings x y := by
  simp only [WallComplement.mem_crossings, imagePrefunctor_obj_val, hW j, ← e.apply_lineMap,
    e.injective.mem_set_image]

end AffineEquiv
