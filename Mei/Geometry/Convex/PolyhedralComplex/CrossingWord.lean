/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.CrossingEvents
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Signed crossing words of polyhedral paths

An admissible segment through the walls of a finite polyhedral complex has a
strictly time-ordered list of crossings. Regular-wall uniqueness ensures that
simultaneous crossings cannot occur, even for coplanar cells, so each signed
crossing event is a singleton. Reading the signed wall generators gives a
free-group word; the first crossing is the rightmost factor, so labels acting on
the left compose in traversal order.

Polygonal crossing words respect concatenation and reversal. Coorientations are
linear functionals with kernel the wall direction. Positive rescaling preserves
the word. These words allow arbitrary group-valued wall labels to be evaluated
without imposing relations between distinct walls.

The construction uses Mathlib's `Finset.sort`, `List.prod`, `FreeGroup.of` and
`Quiver.Path`, together with the regular-wall uniqueness theorem for complexes.

The sequence crossing-word formula is adapted from Codex,
[Mei PR #325](https://github.com/yuma-mizuno-lean/Mei/pull/325).
-/

public section

noncomputable section

open Set
open Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Crossing time determines the wall of an admissible segment through a complex. -/
theorem crossing_time_injective (e : x ⟶ y) :
    Function.Injective (fun a : WallComplement.crossings x y => a.val.2) := by
  intro a b hab
  have ha := (WallComplement.mem_crossings x y a.val.1 a.val.2).mp a.property
  have hb := (WallComplement.mem_crossings x y b.val.1 b.val.2).mp b.property
  apply Subtype.ext
  apply Prod.ext
  · exact C.eq_of_mem_wall_of_notMem_singularSupport ha.2
      (by simpa only [hab] using hb.2) (e.down.regular _ ha.1)
  · exact hab

/-- At a crossing of an admissible segment through a complex, the signed crossing event
consists of the crossed wall alone, with its crossing exponent. -/
theorem signedCrossingEvent_eq_singleton (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    {Q : C.walls} {t : ℝ} (hQ : (Q, t) ∈ WallComplement.crossings x y) :
    WallComplement.signedCrossingEvent ν x y t =
      {(Q, if 0 < ν Q (y.val - x.val) then -1 else 1)} := by
  ext ⟨Q', z⟩
  rw [WallComplement.mem_signedCrossingEvent, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hQ', hz⟩
    obtain rfl : Q' = Q := congrArg (fun b => b.val.1)
      (C.crossing_time_injective e (a₁ := ⟨(Q', t), hQ'⟩) (a₂ := ⟨(Q, t), hQ⟩) rfl)
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hQ, rfl⟩

/-- The crossings of an admissible segment in strictly increasing time order. -/
def orderedCrossings (e : x ⟶ y) : List (C.walls × ℝ) := by
  classical
  letI := (e.down.finite_crossings).fintype
  let r := fun a b : WallComplement.crossings x y => a.val.2 ≤ b.val.2
  haveI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  haveI : Std.Antisymm r := ⟨fun a b hab hba =>
    C.crossing_time_injective e (le_antisymm hab hba)⟩
  haveI : Std.Total r := ⟨fun a b => le_total a.val.2 b.val.2⟩
  exact ((Finset.univ : Finset (WallComplement.crossings x y)).sort r).map Subtype.val

/-- The ordered list contains exactly the geometric crossings. -/
@[simp]
theorem mem_orderedCrossings (e : x ⟶ y) (a : C.walls × ℝ) :
    a ∈ C.orderedCrossings e ↔ a ∈ WallComplement.crossings x y := by
  classical
  simp [orderedCrossings]

/-- Crossing parameters strictly increase in the ordered list. -/
theorem pairwise_orderedCrossings (e : x ⟶ y) :
    (C.orderedCrossings e).Pairwise (fun a b => a.2 < b.2) := by
  classical
  let := (e.down.finite_crossings).fintype
  let r := fun a b : WallComplement.crossings x y => a.val.2 ≤ b.val.2
  have : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  have : Std.Antisymm r := ⟨fun a b hab hba =>
    C.crossing_time_injective e (le_antisymm hab hba)⟩
  have : Std.Total r := ⟨fun a b => le_total a.val.2 b.val.2⟩
  have hle := Finset.pairwise_sort (Finset.univ : Finset (WallComplement.crossings x y)) r
  have hne := List.nodup_iff_pairwise_ne.mp
    (Finset.sort_nodup (Finset.univ : Finset (WallComplement.crossings x y)) r)
  exact List.pairwise_map.mpr ((hle.and hne).imp fun {a b} hab =>
    lt_of_le_of_ne hab.1 (fun he => hab.2 (C.crossing_time_injective e he)))

/-- Strict time order and the geometric membership test characterize the crossing list. -/
theorem orderedCrossings_eq_iff (e : x ⟶ y) (l : List (C.walls × ℝ)) :
    l = C.orderedCrossings e ↔ l.Pairwise (fun a b => a.2 < b.2) ∧
      ∀ a, a ∈ l ↔ a ∈ WallComplement.crossings x y := by
  constructor
  · rintro rfl
    exact ⟨C.pairwise_orderedCrossings e, C.mem_orderedCrossings e⟩
  · rintro ⟨hpair, hmem⟩
    have : Std.Antisymm (fun a b : C.walls × ℝ => a.2 < b.2) :=
      ⟨fun _ _ hab hba => (lt_asymm hab hba).elim⟩
    have : Std.Irrefl (fun a b : C.walls × ℝ => a.2 < b.2) := ⟨fun a => lt_irrefl a.2⟩
    exact hpair.eq_of_mem_iff (C.pairwise_orderedCrossings e)
      (fun a => (hmem a).trans (C.mem_orderedCrossings e a).symm)

/-- Reversing a segment reverses its crossing list and replaces `t` by `1 - t`. -/
theorem orderedCrossings_reverse (e : x ⟶ y) :
    C.orderedCrossings (Quiver.reverse e) =
      ((C.orderedCrossings e).reverse.map fun a => (a.1, 1 - a.2)) := by
  have hpair : (((C.orderedCrossings e).reverse.map fun a => (a.1, 1 - a.2))).Pairwise
      (fun a b => a.2 < b.2) := by
    apply List.pairwise_map.mpr
    exact (C.pairwise_orderedCrossings e).reverse.imp (by intros; dsimp; linarith)
  have hmem (a : C.walls × ℝ) :
      a ∈ C.orderedCrossings (Quiver.reverse e) ↔
        a ∈ ((C.orderedCrossings e).reverse.map fun a => (a.1, 1 - a.2)) := by
    rcases a with ⟨P, t⟩
    rw [mem_orderedCrossings, WallComplement.mem_crossings_swap]
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · intro ht
      exact ⟨(P, 1 - t), (C.mem_orderedCrossings e _).mpr ht, by simp⟩
    · rintro ⟨⟨Q, s⟩, hs, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simpa only [sub_sub_cancel] using (C.mem_orderedCrossings e _).mp hs
  exact ((C.orderedCrossings_eq_iff _ _).mpr
    ⟨hpair, fun a => (hmem a).symm.trans (C.mem_orderedCrossings _ a)⟩).symm

/-- The signed generator for a crossing: positive normal velocity contributes an
inverse, negative velocity contributes the generator. -/
def crossingLetter (ν : C.walls → V →ₗ[ℝ] ℝ) (x y : WallComplement (fun P : C.walls => (P : Set V)))
    (P : C.walls) : FreeGroup C.walls :=
  if 0 < ν P (y.val - x.val) then (FreeGroup.of P)⁻¹ else FreeGroup.of P

/-- The sign convention defining each crossing letter. -/
theorem crossingLetter_def (ν : C.walls → V →ₗ[ℝ] ℝ)
    (x y : WallComplement (fun P : C.walls => (P : Set V))) (P : C.walls) :
    C.crossingLetter ν x y P =
      if 0 < ν P (y.val - x.val) then (FreeGroup.of P)⁻¹ else FreeGroup.of P := (rfl)

/-- A normal whose kernel is the wall direction is nonzero on a crossing velocity. -/
theorem normal_velocity_ne_zero (ν : V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    {a : C.walls × ℝ} (ha : a ∈ C.orderedCrossings e)
    (hν : LinearMap.ker ν = (affineSpan ℝ (a.1 : Set V)).direction) :
    ν (y.val - x.val) ≠ 0 := by
  have ha' := (WallComplement.mem_crossings x y a.1 a.2).mp
    ((C.mem_orderedCrossings e a).mp ha)
  intro hz
  apply e.down.transverse a.1 ⟨a.2, ha'.1, ha'.2⟩
  rw [← hν]
  exact hz

/-- Reversing a velocity on which the normal is nonzero inverts its letter. -/
theorem crossingLetter_swap (ν : C.walls → V →ₗ[ℝ] ℝ) (P : C.walls)
    (hν : ν P (y.val - x.val) ≠ 0) :
    C.crossingLetter ν y x P = (C.crossingLetter ν x y P)⁻¹ := by
  have he : ν P (x.val - y.val) = -ν P (y.val - x.val) := by simp [map_sub]
  simp only [crossingLetter, he]
  rcases lt_or_gt_of_ne hν with hn | hn
  · simp only [ite_eq_left (neg_pos.mpr hn), ite_eq_right (not_lt_of_ge hn.le)]
  · simp only [ite_eq_left hn, ite_eq_right (not_lt_of_ge (neg_nonpos.mpr hn.le)), inv_inv]

/-- The free-group word of one segment, with the first crossing rightmost. -/
def segmentCrossingWord (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) : FreeGroup C.walls :=
  ((C.orderedCrossings e).reverse.map fun a => C.crossingLetter ν x y a.1).prod

/-- Evaluate a segment word as the product of its time-ordered signed letters,
with the earliest factor on the right. -/
theorem segmentCrossingWord_def (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y) :
    C.segmentCrossingWord ν e =
      ((C.orderedCrossings e).reverse.map fun a => C.crossingLetter ν x y a.1).prod := (rfl)

/-- A segment missing all walls has the empty crossing word. -/
theorem segmentCrossingWord_eq_one (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ y)
    (he : WallComplement.crossings x y = ∅) : C.segmentCrossingWord ν e = 1 := by
  have hl : C.orderedCrossings e = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    simp [he]
  simp [segmentCrossingWord, hl]

/-- Segment reversal inverts its crossing word. -/
@[simp]
theorem segmentCrossingWord_reverse (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    (e : x ⟶ y) :
    C.segmentCrossingWord ν (Quiver.reverse e) = (C.segmentCrossingWord ν e)⁻¹ := by
  have hl : (C.orderedCrossings e).map (fun a => C.crossingLetter ν y x a.1) =
      (C.orderedCrossings e).map (fun a => (C.crossingLetter ν x y a.1)⁻¹) := by
    apply List.map_congr_left
    exact fun a ha => C.crossingLetter_swap ν a.1
      (C.normal_velocity_ne_zero (ν a.1) e ha (hν a.1))
  simp only [segmentCrossingWord, orderedCrossings_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map, Function.comp_def]
  rw [hl, List.prod_inv_reverse]
  simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def]

/-- Positively rescaling the normals leaves every crossing letter unchanged. -/
theorem crossingLetter_smul (ν : C.walls → V →ₗ[ℝ] ℝ) (r : C.walls → ℝ)
    (hr : ∀ P, 0 < r P) (x y : WallComplement (fun P : C.walls => (P : Set V))) (P : C.walls) :
    C.crossingLetter (fun Q => r Q • ν Q) x y P = C.crossingLetter ν x y P := by
  simp [crossingLetter, mul_pos_iff_of_pos_left (hr P)]

/-- Positive rescaling of the coorientations preserves a segment word. -/
@[simp]
theorem segmentCrossingWord_smul (ν : C.walls → V →ₗ[ℝ] ℝ) (r : C.walls → ℝ)
    (hr : ∀ P, 0 < r P) (e : x ⟶ y) :
    C.segmentCrossingWord (fun P => r P • ν P) e = C.segmentCrossingWord ν e := by
  simp only [segmentCrossingWord, crossingLetter_smul C ν r hr]

/-- A stationary segment contributes no crossings, regardless of coorientation. -/
@[simp]
theorem segmentCrossingWord_self (ν : C.walls → V →ₗ[ℝ] ℝ) (e : x ⟶ x) :
    C.segmentCrossingWord ν e = 1 := by
  apply C.segmentCrossingWord_eq_one ν e
  ext ⟨P, t⟩
  simp [WallComplement.mem_crossings, x.notMem P]

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}

variable {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- The signed word of a polygonal path; the first crossing acts first, on the left. -/
def crossingWord : {y : WallComplement (fun P : C.walls => (P : Set V))} →
    AdmissiblePLPath x y → (C.walls → V →ₗ[ℝ] ℝ) → FreeGroup C.walls
  | _, .nil, _ => 1
  | _, .cons q e, ν => C.segmentCrossingWord ν e * crossingWord q ν

/-- Constant paths have empty crossing words. -/
@[simp]
theorem crossingWord_nil (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (Quiver.Path.nil : AdmissiblePLPath x x).crossingWord ν = 1 := (rfl)

/-- Appending a segment places its word on the left. -/
@[simp]
theorem crossingWord_cons (p : AdmissiblePLPath x y) (e : y ⟶ z)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.cons e).crossingWord ν = C.segmentCrossingWord ν e * p.crossingWord ν := (rfl)

/-- Concatenating paths multiplies their words in order of left actions. -/
@[simp]
theorem crossingWord_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (p.comp q).crossingWord ν = q.crossingWord ν * p.crossingWord ν := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, mul_assoc]

/-- Traversing a polygonal path backwards inverts its signed crossing word. -/
@[simp]
theorem crossingWord_reverse (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction) :
    p.reverse.crossingWord ν = (p.crossingWord ν)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, Quiver.Hom.toPath, ih, C.segmentCrossingWord_reverse ν hν]

/-- Positively rescaling each coorientation preserves the polygonal crossing word. -/
@[simp]
theorem crossingWord_smul (p : AdmissiblePLPath x y) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) :
    p.crossingWord (fun P => r P • ν P) = p.crossingWord ν := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, C.segmentCrossingWord_smul ν r hr]

/-- The word along a sequence of edges is the inverse of the increasing-order
product of the inverse edge words, so the first crossing is the rightmost factor. -/
@[simp]
theorem crossingWord_ofSeq
    (x : ℕ → WallComplement (fun P : C.walls => (P : Set V)))
    (e : ∀ j, x j ⟶ x (j + 1)) (n : ℕ) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (ofSeq x e n).crossingWord ν =
      (((List.range n).map fun j => (C.segmentCrossingWord ν (e j))⁻¹).prod)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.prod_range_succ]

end Quiver.Path
