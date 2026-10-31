/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.SideChamber
public import Mei.Geometry.Convex.PolyhedralComplex.SingleCrossing

/-!
# Chamber itineraries of admissible paths

The *crossing letters* of an admissible path through the walls of a finite polyhedral
complex list its crossed walls in traversal order, each with the sign of the normal
velocity: `true` for a crossing in the direction of the coorientation. Unlike the
free-group crossing word, the list retains cancelling crossings. It is multiplicative
under concatenation, reversed with flipped signs by path reversal, and unchanged by
path subdivision. The crossing word is its signed product, with the first crossing
rightmost.

A letter runs from the negative to the positive chamber of its wall when its sign is
`true`, and backwards otherwise. A list of letters is a *crossing chain* from one
chamber to another when each letter starts where the previous one ends. The crossing
letters of every admissible path form a chain from the chamber of its start to the
chamber of its end (`Quiver.Path.isCrossingChain_crossingLetters`): this is the itinerary
of chambers visited by the path. Chamber-valued
data, such as the objects and arrows of a groupoid-labelled wall diagram, can
therefore be composed along admissible paths.

The crossing list uses Mathlib's `Quiver.Path.weight` in the free monoid of signed walls.
The chain property is checked on a subdivision into segments with at most one crossing
(`Quiver.Path.exists_subdivision_subsingleton_crossings`), using the incident chambers
of `FinitePolyhedralComplex.chamber_eq_of_crossings_eq_singleton`. Subdivision
invariance follows the list-level formula `FinitePolyhedralComplex.orderedCrossings_subdivide`.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (C : FinitePolyhedralComplex h)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- The crossed walls of a segment in time order, each marked `true` exactly when the
segment's normal velocity is positive. -/
def segmentCrossingLetters (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) : List (C.walls × Bool) :=
  (C.orderedCrossings e).map fun a => (a.1, decide (0 < ν a.1 (y.val - x.val)))

/-- The crossing letters of a segment, read from its ordered crossing list. -/
theorem segmentCrossingLetters_def (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) :
    C.segmentCrossingLetters ν e =
      (C.orderedCrossings e).map fun a => (a.1, decide (0 < ν a.1 (y.val - x.val))) := (rfl)

/-- Splitting a segment at an interior off-wall point concatenates its crossing letters. -/
theorem segmentCrossingLetters_subdivide (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) :
    C.segmentCrossingLetters ν e =
      C.segmentCrossingLetters ν e₁ ++ C.segmentCrossingLetters ν e₂ := by
  have h₁ : z.val - x.val = t • (y.val - x.val) := by
    rw [hz, AffineMap.lineMap_apply_module']
    abel
  have h₂ : y.val - z.val = (1 - t) • (y.val - x.val) := by
    rw [hz]
    exact AffineMap.right_vsub_lineMap x.val y.val t
  have hpos₁ (P : C.walls) : (0 < ν P (z.val - x.val)) = (0 < ν P (y.val - x.val)) := by
    rw [h₁, map_smul, smul_eq_mul, mul_pos_iff_of_pos_left ht.1]
  have hpos₂ (P : C.walls) : (0 < ν P (y.val - z.val)) = (0 < ν P (y.val - x.val)) := by
    rw [h₂, map_smul, smul_eq_mul, mul_pos_iff_of_pos_left (sub_pos.mpr ht.2)]
  simp only [segmentCrossingLetters_def, C.orderedCrossings_subdivide e e₁ e₂ ht hz,
    List.map_append, List.map_map, Function.comp_def, hpos₁, hpos₂]

/-- Reversing a segment reverses its crossing letters and flips their signs. -/
theorem segmentCrossingLetters_reverse (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) (e : x ⟶ y) :
    C.segmentCrossingLetters ν (Quiver.reverse e) =
      (C.segmentCrossingLetters ν e).reverse.map fun l => (l.1, !l.2) := by
  rw [segmentCrossingLetters_def, segmentCrossingLetters_def, orderedCrossings_reverse]
  simp only [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hne := C.normal_velocity_ne_zero (ν a.1) e ha (hν a.1)
  have hneg : ν a.1 (x.val - y.val) = -ν a.1 (y.val - x.val) := by
    rw [← map_neg, neg_sub]
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  rw [hneg]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [decide_eq_true (neg_pos.mpr hlt), decide_eq_false (not_lt_of_gt hlt)]
    rfl
  · rw [decide_eq_false (not_lt.mpr (neg_nonpos.mpr hgt.le)), decide_eq_true hgt]
    rfl

/-- The chamber at which a crossing letter starts: the negative chamber of its wall for
a crossing along the coorientation, the positive chamber otherwise. -/
-- Reducible and exposed, so that arrows between the objects of these chambers type-check
-- by computation and their endpoint identities are found by `simp`.
@[expose, reducible]
def crossingSource (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    C.walls × Bool → Chamber (fun P : C.walls => (P : Set V))
  | (P, true) => C.negativeChamber P (ν P) (hν P)
  | (P, false) => C.positiveChamber P (ν P) (hν P)

/-- The chamber at which a crossing letter ends. -/
-- Reducible and exposed, as for `crossingSource`.
@[expose, reducible]
def crossingTarget (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    C.walls × Bool → Chamber (fun P : C.walls => (P : Set V))
  | (P, true) => C.positiveChamber P (ν P) (hν P)
  | (P, false) => C.negativeChamber P (ν P) (hν P)

/-- Flipping the sign of a letter exchanges its source and target. -/
@[simp]
theorem crossingSource_flip (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (l : C.walls × Bool) : C.crossingSource ν hν (l.1, !l.2) = C.crossingTarget ν hν l := by
  obtain ⟨P, _ | _⟩ := l <;> rfl

/-- Flipping the sign of a letter exchanges its target and source. -/
@[simp]
theorem crossingTarget_flip (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (l : C.walls × Bool) : C.crossingTarget ν hν (l.1, !l.2) = C.crossingSource ν hν l := by
  obtain ⟨P, _ | _⟩ := l <;> rfl

/-- A list of crossing letters is a chain from `a` to `b` when each letter starts at the
chamber where the previous letter ends; the empty chain requires `a = b`. -/
def IsCrossingChain (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    Chamber (fun P : C.walls => (P : Set V)) → Chamber (fun P : C.walls => (P : Set V)) →
      List (C.walls × Bool) → Prop
  | a, b, [] => a = b
  | a, b, l :: L => a = C.crossingSource ν hν l ∧ IsCrossingChain ν hν (C.crossingTarget ν hν l) b L

variable {C} {ν : C.walls → V →ₗ[ℝ] ℝ}
  {hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction}
  {a b : Chamber (fun P : C.walls => (P : Set V))}

/-- The empty letter list is a chain exactly between equal chambers. -/
@[simp]
theorem isCrossingChain_nil : C.IsCrossingChain ν hν a b [] ↔ a = b := Iff.rfl

/-- A chain starts at the source of its first letter and continues from its target. -/
@[simp]
theorem isCrossingChain_cons (l : C.walls × Bool) (L : List (C.walls × Bool)) :
    C.IsCrossingChain ν hν a b (l :: L) ↔
      a = C.crossingSource ν hν l ∧ C.IsCrossingChain ν hν (C.crossingTarget ν hν l) b L :=
  Iff.rfl

/-- A concatenation is a chain exactly when it passes through an intermediate chamber. -/
theorem isCrossingChain_append {L₁ L₂ : List (C.walls × Bool)} :
    C.IsCrossingChain ν hν a b (L₁ ++ L₂) ↔
      ∃ c, C.IsCrossingChain ν hν a c L₁ ∧ C.IsCrossingChain ν hν c b L₂ := by
  induction L₁ generalizing a with
  | nil => simp
  | cons l L₁ ih =>
    simp only [List.cons_append, isCrossingChain_cons, ih]
    constructor
    · rintro ⟨rfl, c, h₁, h₂⟩
      exact ⟨c, ⟨rfl, h₁⟩, h₂⟩
    · rintro ⟨c, ⟨rfl, h₁⟩, h₂⟩
      exact ⟨rfl, c, h₁, h₂⟩

/-- Reversing a chain and flipping its signs gives a chain in the opposite direction. -/
theorem IsCrossingChain.reverse {L : List (C.walls × Bool)}
    (hL : C.IsCrossingChain ν hν a b L) :
    C.IsCrossingChain ν hν b a (L.reverse.map fun l => (l.1, !l.2)) := by
  induction L generalizing a with
  | nil => exact hL.symm
  | cons l L ih =>
    obtain ⟨rfl, hL⟩ := hL
    rw [List.reverse_cons, List.map_append, isCrossingChain_append]
    exact ⟨_, ih hL, by simp⟩

/-- An admissible segment meeting at most one wall has a chain of crossing letters from
the chamber of its start to the chamber of its end. -/
theorem isCrossingChain_segmentCrossingLetters_of_subsingleton (e : x ⟶ y)
    (he : (WallComplement.crossings x y).Subsingleton) :
    C.IsCrossingChain ν hν (chamber x) (chamber y) (C.segmentCrossingLetters ν e) := by
  rcases he.eq_empty_or_singleton with he | ⟨⟨P, t⟩, he⟩
  · have hl : C.orderedCrossings e = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      simp [he]
    simpa [segmentCrossingLetters_def, hl] using chamber_eq_of_crossings_eq_empty he
  · have hl : C.orderedCrossings e = [(P, t)] := by
      symm
      apply (C.orderedCrossings_eq_iff e _).mpr
      simp [he]
    have hne := C.normal_velocity_ne_zero (ν P) e (a := (P, t))
      (by rw [hl]; exact List.mem_singleton_self _) (hν P)
    simp only [segmentCrossingLetters_def, hl, List.map_cons, List.map_nil,
      isCrossingChain_cons, isCrossingChain_nil]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- Crossing against the coorientation: read the reversed segment.
      have hrev : WallComplement.crossings y x = {(P, 1 - t)} := by
        rw [WallComplement.crossings_swap, he, image_singleton]
      have hv : 0 < ν P (x.val - y.val) := by
        rw [← neg_sub, map_neg]
        exact neg_pos.mpr hlt
      obtain ⟨hy, hx⟩ := C.chamber_eq_of_crossings_eq_singleton (Quiver.reverse e) hrev
        (hν P) hv
      simp only [not_lt_of_gt hlt, decide_false]
      exact ⟨hx, hy.symm⟩
    · obtain ⟨hx, hy⟩ := C.chamber_eq_of_crossings_eq_singleton e he (hν P) hgt
      simp only [hgt, decide_true]
      exact ⟨hx, hy.symm⟩

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

open Mei Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h}
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- The crossing letters of a polygonal path, in traversal order. -/
def crossingLetters (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    List (C.walls × Bool) :=
  FreeMonoid.toList (p.weight (fun e => FreeMonoid.ofList (C.segmentCrossingLetters ν e)))

/-- Constant paths have no crossing letters. -/
@[simp]
theorem crossingLetters_nil (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (Quiver.Path.nil : AdmissiblePLPath x x).crossingLetters ν = [] := by
  simp [crossingLetters, weight_nil]

/-- Appending a segment appends its crossing letters. -/
@[simp]
theorem crossingLetters_cons (p : AdmissiblePLPath x y) (e : y ⟶ z)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.cons e).crossingLetters ν = p.crossingLetters ν ++ C.segmentCrossingLetters ν e := by
  simp [crossingLetters, weight_cons]

/-- A one-segment path has the crossing letters of its segment. -/
@[simp]
theorem crossingLetters_toPath (e : x ⟶ y) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    e.toPath.crossingLetters ν = C.segmentCrossingLetters ν e := by
  simp [Quiver.Hom.toPath]

/-- Concatenating paths concatenates their crossing letters. -/
@[simp]
theorem crossingLetters_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.comp q).crossingLetters ν = p.crossingLetters ν ++ q.crossingLetters ν := by
  simp [crossingLetters, weight_comp]

/-- Reversing a path reverses its crossing letters and flips their signs. -/
theorem crossingLetters_reverse (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    p.reverse.crossingLetters ν = (p.crossingLetters ν).reverse.map fun l => (l.1, !l.2) := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, ih, C.segmentCrossingLetters_reverse ν hν]

/-- Subdividing a polygonal path preserves its crossing letters. -/
theorem IsSubdivision.crossingLetters_eq {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    q.crossingLetters ν = p.crossingLetters ν := by
  induction hpq with
  | refl p => rfl
  | split e e₁ e₂ ht hz =>
    simp [C.segmentCrossingLetters_subdivide ν e e₁ e₂ ht hz]
  | comp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | trans _ _ ih₁ ih₂ => rw [ih₂, ih₁]

/-- The crossing word is the signed product of the crossing letters, with the first
crossing rightmost and a positive normal velocity contributing an inverse generator. -/
theorem crossingWord_eq_prod_crossingLetters (p : AdmissiblePLPath x y)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    p.crossingWord ν = ((p.crossingLetters ν).reverse.map fun l =>
      if l.2 then (FreeGroup.of l.1)⁻¹ else FreeGroup.of l.1).prod := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [crossingWord_cons, ih, crossingLetters_cons, List.reverse_append, List.map_append,
      List.prod_append]
    congr 1
    simp only [segmentCrossingWord_def, segmentCrossingLetters_def, List.map_reverse,
      List.map_map]
    congr 2
    apply List.map_congr_left
    intro a _
    simp [crossingLetter_def]

/-- The crossing letters of an admissible path form a chain from the chamber of its start
to the chamber of its end. -/
theorem isCrossingChain_crossingLetters (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    C.IsCrossingChain ν hν (chamber x) (chamber y) (p.crossingLetters ν) := by
  obtain ⟨q, hq, hsmall⟩ := p.exists_subdivision_subsingleton_crossings
  rw [← hq.crossingLetters_eq ν]
  clear hq p
  induction q with
  | nil => simp
  | @cons y z q e ih =>
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.isChain_vertices_comp] at hsmall
    simp only [Quiver.Path.vertices_toPath, List.isChain_pair] at hsmall
    rw [crossingLetters_cons, isCrossingChain_append]
    exact ⟨_, ih hsmall.1,
      isCrossingChain_segmentCrossingLetters_of_subsingleton e hsmall.2⟩

end Quiver.Path
