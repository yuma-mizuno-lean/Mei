/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision

/-!
# Finite wall diagrams and path products

A finite wall diagram labels the walls of a fixed polyhedral complex in a group.
Coorientations are represented by linear functionals whose kernels are the wall
directions. Evaluating the signed crossing word gives the path product, with the
first crossing rightmost. Products respect concatenation, reversal, path subdivision
and relabelling.
Positive rescaling of normals, or reversing chosen normals while inverting their
labels, preserves every path product. Consistency means endpoint independence;
it is equivalent to triviality of all admissible loop products.

The construction uses Mathlib's `FreeGroup.lift` and the signed polygonal crossing
words in `Mei.Geometry.Convex.PolyhedralComplex.CrossingWord`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Group labels and coorientation representatives on the walls of a finite complex.
Only actual walls carry data; positive rescaling does not change path products. -/
@[ext]
structure FiniteWallDiagram (C : FinitePolyhedralComplex h) (H : Type*) where
  /-- A linear representative of the coorientation of each wall. -/
  normal : C.walls → V →ₗ[ℝ] ℝ
  /-- The normal cuts out exactly the wall direction. -/
  ker_normal : ∀ P, LinearMap.ker (normal P) = (affineSpan ℝ (P : Set V)).direction
  /-- The group element attached to each wall. -/
  label : C.walls → H

namespace FiniteWallDiagram

variable {C : FinitePolyhedralComplex h} {H K J : Type*}
  [Group H] [Group K] [Group J]
  (D : FiniteWallDiagram C H)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

omit [Group H] in
/-- Every coorientation representative is nonzero, since a wall has codimension one. -/
theorem normal_ne_zero (P : C.walls) : D.normal P ≠ 0 := by
  intro hn
  have hd := C.finrank_direction_add_one_of_mem_walls P.property
  rw [← D.ker_normal P, hn] at hd
  rw [LinearMap.ker_zero, finrank_top] at hd
  omega

/-- Evaluate the signed crossing word in the group of wall labels. -/
def pathProduct (p : AdmissiblePLPath x y) : H :=
  FreeGroup.lift D.label (p.crossingWord D.normal)

/-- The crossing-word characterization of the path product. -/
theorem pathProduct_def (p : AdmissiblePLPath x y) :
    D.pathProduct p = FreeGroup.lift D.label (p.crossingWord D.normal) := (rfl)

@[simp]
theorem pathProduct_nil :
    D.pathProduct (Quiver.Path.nil : AdmissiblePLPath x x) = 1 := by
  simp [pathProduct]

/-- Appending a segment places its signed crossing product on the left. -/
@[simp]
theorem pathProduct_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    D.pathProduct (p.cons e) =
      D.pathProduct e.toPath * D.pathProduct p := by
  simp [pathProduct, Quiver.Hom.toPath]

/-- Successive paths act in traversal order: the second path's product is leftmost. -/
@[simp]
theorem pathProduct_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.pathProduct (p.comp q) = D.pathProduct q * D.pathProduct p := by
  simp [pathProduct]

/-- Subdividing a polygonal path by allowed interior vertices preserves its product. -/
theorem pathProduct_eq_of_isSubdivision {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) : D.pathProduct q = D.pathProduct p := by
  rw [pathProduct_def, pathProduct_def, hpq.crossingWord_eq]

/-- Reversal inverts the entire path product. -/
@[simp]
theorem pathProduct_reverse (p : AdmissiblePLPath x y) :
    D.pathProduct p.reverse = (D.pathProduct p)⁻¹ := by
  simp [pathProduct, p.crossingWord_reverse D.normal D.ker_normal]

/-- The product on a single segment, in decreasing crossing-time order. -/
theorem pathProduct_toPath (e : x ⟶ y) :
    D.pathProduct e.toPath = ((C.orderedCrossings e).reverse.map fun a =>
      if 0 < D.normal a.1 (y.val - x.val) then (D.label a.1)⁻¹ else D.label a.1).prod := by
  simp [Quiver.Hom.toPath, pathProduct, C.segmentCrossingWord_def,
    MonoidHom.map_list_prod, List.map_map, C.crossingLetter_def, Function.comp_def, apply_ite]

/-- A segment meeting no wall has trivial product. -/
theorem pathProduct_toPath_eq_one (e : x ⟶ y) (he : WallComplement.crossings x y = ∅) :
    D.pathProduct e.toPath = 1 := by
  simp [pathProduct, Quiver.Hom.toPath, C.segmentCrossingWord_eq_one D.normal e he]

/-- Change every wall label by a group homomorphism. -/
def relabel (f : H →* K) : FiniteWallDiagram C K where
  normal := D.normal
  ker_normal := D.ker_normal
  label P := f (D.label P)

@[simp]
theorem relabel_normal (f : H →* K) : (D.relabel f).normal = D.normal := (rfl)

@[simp]
theorem relabel_label (f : H →* K) (P : C.walls) :
    (D.relabel f).label P = f (D.label P) := (rfl)

@[simp]
theorem relabel_id : D.relabel (MonoidHom.id H) = D := by ext <;> rfl

@[simp]
theorem relabel_comp (f : H →* K) (g : K →* J) :
    (D.relabel f).relabel g = D.relabel (g.comp f) := by ext <;> rfl

/-- Relabelling commutes with every admissible path product. -/
@[simp]
theorem pathProduct_relabel (f : H →* K) (p : AdmissiblePLPath x y) :
    (D.relabel f).pathProduct p = f (D.pathProduct p) := by
  exact (FreeGroup.lift_unique (f.comp (FreeGroup.lift D.label)) (by simp)).symm

omit [Group H] in
/-- Choose a positive multiple of each coorientation representative. -/
def rescale (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) : FiniteWallDiagram C H where
  normal P := r P • D.normal P
  ker_normal P := by
    rw [← D.ker_normal P]
    ext v
    simp [LinearMap.mem_ker, (hr P).ne']
  label := D.label

omit [Group H] in
@[simp]
theorem rescale_normal (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) :
    (D.rescale r hr).normal = fun P => r P • D.normal P := (rfl)

omit [Group H] in
@[simp]
theorem rescale_label (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) :
    (D.rescale r hr).label = D.label := (rfl)

/-- Path products depend only on the coorientation, not its positive scale. -/
@[simp]
theorem pathProduct_rescale (r : C.walls → ℝ) (hr : ∀ P, 0 < r P)
    (p : AdmissiblePLPath x y) : (D.rescale r hr).pathProduct p = D.pathProduct p := by
  simp [pathProduct, p.crossingWord_smul D.normal r hr]

/-- Reverse selected normals and invert exactly their labels. -/
def reorient (s : C.walls → Bool) : FiniteWallDiagram C H where
  normal P := if s P then -D.normal P else D.normal P
  ker_normal P := by split <;> simp_all [D.ker_normal]
  label P := if s P then (D.label P)⁻¹ else D.label P

@[simp]
theorem reorient_normal (s : C.walls → Bool) (P : C.walls) :
    (D.reorient s).normal P = (if s P then -D.normal P else D.normal P) := (rfl)

@[simp]
theorem reorient_label (s : C.walls → Bool) (P : C.walls) :
    (D.reorient s).label P = (if s P then (D.label P)⁻¹ else D.label P) := (rfl)

/-- Changing a wall's coorientation and label together preserves its contribution. -/
private theorem pathProduct_reorient_toPath (s : C.walls → Bool) (e : x ⟶ y) :
    (D.reorient s).pathProduct e.toPath = D.pathProduct e.toPath := by
  rw [pathProduct_toPath, pathProduct_toPath]
  congr 1
  apply List.map_congr_left
  intro a ha
  have ha' : a ∈ C.orderedCrossings e := List.mem_reverse.mp ha
  have hn := C.normal_velocity_ne_zero (D.normal a.1) e ha' (D.ker_normal a.1)
  simp only [reorient_normal, reorient_label]
  cases hs : s a.1 with
  | false => simp
  | true =>
    simp only [↓reduceIte, LinearMap.neg_apply]
    rcases lt_or_gt_of_ne hn with hn | hn
    · simp only [neg_pos.mpr hn, not_lt_of_ge hn.le, ↓reduceIte, inv_inv]
    · simp only [not_lt_of_ge (neg_nonpos.mpr hn.le), hn, ↓reduceIte]

/-- Simultaneous reversal of any selected coorientations and labels preserves products. -/
@[simp]
theorem pathProduct_reorient (s : C.walls → Bool) (p : AdmissiblePLPath x y) :
    (D.reorient s).pathProduct p = D.pathProduct p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    have he := D.pathProduct_reorient_toPath s e
    simp only [pathProduct_cons, ih, he]

/-- A diagram is consistent when its products depend only on the endpoints. -/
def Consistent : Prop :=
  ∀ ⦃x y : WallComplement (fun P : C.walls => (P : Set V))⦄
    (p q : AdmissiblePLPath x y), D.pathProduct p = D.pathProduct q

/-- The endpoint-independence characterization of consistency. -/
theorem consistent_def : D.Consistent ↔
    ∀ ⦃x y : WallComplement (fun P : C.walls => (P : Set V))⦄
      (p q : AdmissiblePLPath x y), D.pathProduct p = D.pathProduct q := Iff.rfl

/-- Consistency is equivalent to the vanishing of all admissible loop products. -/
theorem consistent_iff_loops : D.Consistent ↔
    ∀ (x : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath x x), D.pathProduct p = 1 := by
  constructor
  · intro hc x p
    simpa using hc p .nil
  · intro hc x y p q
    have he := hc x (p.comp q.reverse)
    exact (inv_mul_eq_one.mp (by simpa only [pathProduct_comp, pathProduct_reverse] using he)).symm

variable {D} in
/-- A homomorphism of label groups preserves consistency. -/
theorem Consistent.relabel (hc : D.Consistent) (f : H →* K) : (D.relabel f).Consistent := by
  intro x y p q
  simpa only [pathProduct_relabel] using congrArg f (hc p q)

/-- A faithful relabelling reflects consistency. -/
theorem consistent_relabel_iff (f : H →* K) (hf : Function.Injective f) :
    (D.relabel f).Consistent ↔ D.Consistent := by
  constructor
  · intro hc x y p q
    apply hf
    simpa only [pathProduct_relabel] using hc p q
  · exact fun hc => hc.relabel f

end FiniteWallDiagram
end Mei
