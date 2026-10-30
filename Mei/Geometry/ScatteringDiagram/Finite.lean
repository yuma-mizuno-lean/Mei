/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Joint
public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.TriangleReduction
public import Mei.Geometry.Convex.Polyhedron.Path.Product

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
It suffices to test three-edge loops: admissible spokes to a common apex reduce
every polygonal loop to triangular relations. When the complex covers the ambient space,
it suffices to test the isolating triangular meridians of its joints.

The construction uses Mathlib's `FreeGroup.lift` and the signed polygonal crossing
words in `Mei.Geometry.Convex.PolyhedralComplex.CrossingWord`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

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

/-- Splitting a segment at an off-wall point places the second segment's product
on the left. -/
theorem pathProduct_subdivide
    {a : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) (e₁ : x ⟶ a) (e₂ : a ⟶ y) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ha : a.val = AffineMap.lineMap x.val y.val t) :
    D.pathProduct e.toPath = D.pathProduct e₂.toPath * D.pathProduct e₁.toPath := by
  simp only [pathProduct_def, Quiver.Hom.toPath, Quiver.Path.crossingWord_cons,
    Quiver.Path.crossingWord_nil, mul_one]
  rw [C.segmentCrossingWord_subdivide D.normal e e₁ e₂ ht ha, map_mul]

/-- For two ordered off-wall points on a segment, transport to the later point
factors through transport to the earlier point. -/
theorem pathProduct_prefix
    {a b : WallComplement (fun P : C.walls => (P : Set V))}
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (ha : a.val = AffineMap.lineMap x.val y.val s)
    (hb : b.val = AffineMap.lineMap x.val y.val t)
    (e₁ : x ⟶ a) (e₂ : x ⟶ b) (e₁₂ : a ⟶ b) :
    D.pathProduct e₂.toPath = D.pathProduct e₁₂.toPath * D.pathProduct e₁.toPath := by
  by_cases hz : t = 0
  · have hs0 : s = 0 := le_antisymm (hst.trans_eq hz) hs.1
    apply D.pathProduct_subdivide e₂ e₁ e₁₂ (t := 0) ⟨le_rfl, zero_le_one⟩
    simp only [AffineMap.lineMap_apply_zero, ha, hs0]
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    apply D.pathProduct_subdivide e₂ e₁ e₁₂ (t := s / t)
      ⟨div_nonneg hs.1 hpos.le, (div_le_one hpos).mpr hst⟩
    rw [ha, hb, AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ hz]

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

/-- The crossing-word product agrees with the indexed simultaneous-event product.
The commutation hypothesis is needed by the latter interface; regular crossings
of a complex contain only one wall. -/
theorem pathProduct_eq_wallPathProduct
    (comm : ∀ a b : C.walls,
      affineSpan ℝ (a : Set V) = affineSpan ℝ (b : Set V) →
        Commute (D.label a) (D.label b)) (p : AdmissiblePLPath x y) :
    D.pathProduct p = p.wallPathProduct D.normal D.label comm := by
  have hsegment {x y : WallComplement (fun P : C.walls => (P : Set V))}
      (e : x ⟶ y) : D.pathProduct e.toPath =
        e.toPath.wallPathProduct D.normal D.label comm := by
    let T := (C.orderedCrossings e).map Prod.snd
    have hT : T.Pairwise (· < ·) := List.pairwise_map.mpr (C.pairwise_orderedCrossings e)
    have hcover : ∀ t ∈ orderedCrossingTimes e, t ∈ T := by
      intro t ht
      obtain ⟨Q, hQ⟩ := (mem_orderedCrossingTimes e t).mp ht
      exact List.mem_map.mpr ⟨(Q, t), (C.mem_orderedCrossings e _).mpr hQ, rfl⟩
    rw [pathProduct_toPath, Quiver.Path.wallPathProduct_toPath,
      segmentPathProduct_eq_prod_of_crossingTimes D.normal D.label comm e T hT hcover]
    simp only [T, List.map_reverse, List.map_map, Function.comp_def]
    apply congrArg List.prod
    apply congrArg List.reverse
    apply List.map_congr_left
    intro a ha
    have ha' := (C.mem_orderedCrossings e a).mp ha
    rw [crossingEventProduct_singleton D.normal D.label comm e a.2 _
      (C.signedCrossingEvent_eq_singleton D.normal e ha')]
    split_ifs <;> simp
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [pathProduct_cons, ← Quiver.Path.comp_toPath_eq_cons,
      Quiver.Path.wallPathProduct_comp, ih, hsegment]

/-- A path product lies in every subgroup containing the labels of all crossed walls. -/
theorem pathProduct_mem {S : Subgroup H} (p : AdmissiblePLPath x y)
    (hS : ∀ a ∈ p.crossingEvents, D.label a.2.1 ∈ S) : D.pathProduct p ∈ S := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [pathProduct_cons]
    refine S.mul_mem ?_ (ih fun a ha => hS a
      ((Quiver.Path.mem_crossingEvents_cons p e a.1 a.2.1 a.2.2).mpr (Or.inl ha)))
    rw [pathProduct_toPath]
    refine S.list_prod_mem fun g hg => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have hl : D.label a.1 ∈ S := hS (p.length, a)
      ((Quiver.Path.mem_crossingEvents_cons p e _ a.1 a.2).mpr (Or.inr ⟨rfl,
        (C.mem_orderedCrossings e a).mp (List.mem_reverse.mp ha)⟩))
    split
    · exact S.inv_mem hl
    · exact hl

/-- A segment meeting no wall has trivial product. -/
theorem pathProduct_toPath_eq_one (e : x ⟶ y) (he : WallComplement.crossings x y = ∅) :
    D.pathProduct e.toPath = 1 := by
  have hl : C.orderedCrossings e = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    simp [he]
  simp [pathProduct_toPath, hl]

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

/-- Consistency can be tested on admissible three-edge loops. The triangles may
contain several joints; `consistent_iff_jointMeridianWords` reduces them to local meridians. -/
theorem consistent_iff_triangles : D.Consistent ↔
    ∀ (x y z : WallComplement (fun P : C.walls => (P : Set V)))
      (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x),
      D.pathProduct ((e.toPath.cons f).cons r) = 1 := by
  constructor
  · intro hD x y z e f r
    exact D.consistent_iff_loops.mp hD x _
  · intro htri
    apply D.consistent_iff_loops.mpr
    intro x p
    rw [pathProduct_def, ← MonoidHom.mem_ker]
    apply Subgroup.normalClosure_le_normal (N := (FreeGroup.lift D.label).ker) ?_
      (p.crossingWord_mem_normalClosure_triangles D.normal D.ker_normal
        isOpen_univ (fun _ _ => mem_univ _))
    intro g hg
    obtain ⟨a, b, c, e, f, r, _, _, _, rfl⟩ := (C.mem_triangleWords D.normal univ g).mp hg
    apply MonoidHom.mem_ker.mpr
    simpa only [pathProduct_def] using htri a b c e f r

/-- For a complex covering the ambient space, a diagram is consistent exactly when its
labels kill the words of the isolating triangular meridians of all joints. -/
theorem consistent_iff_jointMeridianWords (hC : C.support = univ) :
    D.Consistent ↔ ∀ g ∈ C.jointMeridianWords D.normal univ, FreeGroup.lift D.label g = 1 := by
  constructor
  · intro hD g hg
    obtain ⟨x, y, z, e, f, r, hx, hy, hz, rfl⟩ :=
      (C.mem_triangleWords D.normal univ g).mp
        (C.jointMeridianWords_subset_triangleWords D.normal univ hg)
    simpa only [pathProduct_def] using
      D.consistent_iff_loops.mp hD x ((e.toPath.cons f).cons r)
  · intro hmer
    apply D.consistent_iff_loops.mpr
    intro x p
    rw [pathProduct_def, ← MonoidHom.mem_ker]
    exact Subgroup.normalClosure_le_normal (N := (FreeGroup.lift D.label).ker)
      (fun g hg => MonoidHom.mem_ker.mpr (hmer g hg))
      (p.crossingWord_mem_normalClosure_jointMeridianWords hC D.normal D.ker_normal
        isOpen_univ convex_univ (fun _ _ => mem_univ _))

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
