/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.Polyhedron.Path.Sum
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Intersection pairings and additive wall transport

An admissible segment is an affine test transverse to every oriented wall cell.
Its intersection pairing is the negative of the additive wall-crossing sum:
intersection indices use the orientation sign, whereas left wall actions use
its negative. Indexed coincident cells retain all their contributions.

These formulas connect geometric cochain relations with additive transport.
Equal finite wall presentations give equal crossing sums on every common
admissible polygonal vertex list. In particular, a presentation representing
the zero cochain has zero crossing sum along every admissible polygonal path.
This allows cochain cancellation to be used for central wall corrections.

The segment endpoint formula uses `WallComplement.crossingExponent_eq_side_sub`.
The comparison uses `OrientedCell.intersectionPairing` and its invariance under
cochain relations, `WallComplement.wallCrossingSum_toPath`, and Mathlib's
`Quiver.Path.addWeightOfEPs` to sum the segment pairings.
-/

public section

noncomputable section

open Set Mei Mei.Convex

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- When a wall agrees with a cooriented hyperplane along a segment, its
intersection index is the increase of the positive-side indicator. The segment's
endpoints must miss the hyperplane. -/
theorem intersectionIndex_eq_sub_side (σ : OrientedCell h 1)
    (ν : V →ₗ[ℝ] ℝ) (b : ℝ) {x y : V} (hx : ν x ≠ b) (hy : ν y ≠ b)
    (hν : ∀ w, SignType.sign (ν w) = σ.orientation.evalSign (fun _ : Fin 1 => w))
    (hlocal : segment ℝ x y ∩ σ.carrier = segment ℝ x y ∩ {z | ν z = b}) :
    σ.intersectionIndex ![x, y] =
      (if b < ν y then 1 else 0 : ℤ) - (if b < ν x then 1 else 0) := by
  classical
  let W : Unit → Set V := fun _ => {z | ν z = b}
  let a : WallComplement W := ⟨x, fun _ => hx⟩
  let c : WallComplement W := ⟨y, fun _ => hy⟩
  have hc := WallComplement.crossingExponent_eq_side_sub a c ν b () rfl
  dsimp only [a, c] at hc
  have hm : (convexHull ℝ (range ![x, y]) ∩ σ.carrier).Nonempty ↔
      ∃ t, ((), t) ∈ WallComplement.crossings a c := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair, hlocal, segment_eq_image_lineMap]
    simp only [WallComplement.mem_crossings]
    exact Set.image_inter_nonempty_iff
  have hframe : (fun j : Fin 1 => ![x, y] j.succ - ![x, y] 0) =
      fun _ : Fin 1 => y - x := by ext j; fin_cases j; rfl
  by_cases hmeet : (convexHull ℝ (range ![x, y]) ∩ σ.carrier).Nonempty
  · rw [intersectionIndex_of_nonempty hmeet, hframe, ← hν]
    rw [ite_eq_left (hm.mp hmeet)] at hc
    have hn : ν y - ν x ≠ 0 := by
      intro he
      have ht := hm.mp hmeet
      obtain ⟨t, ht⟩ := ht
      have htb := ((WallComplement.mem_crossings a c () t).mp ht).2
      simp only [W, mem_ofPred_eq, a, c, AffineMap.lineMap_apply_module',
        map_add, map_smul, map_sub, smul_eq_mul] at htb
      exact hx (by simpa only [he, mul_zero, zero_add] using htb)
    rw [map_sub]
    rcases lt_or_gt_of_ne hn with hn | hn
    · simp only [sign_neg hn, SignType.coe_neg_one]
      simp only [map_sub, ite_eq_right (by linarith : ¬0 < ν y - ν x)] at hc
      omega
    · simp only [sign_pos hn, SignType.coe_one]
      simp only [map_sub, ite_eq_left hn] at hc
      omega
  · rw [intersectionIndex_of_disjoint
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))]
    rw [ite_eq_right (hm.not.mp hmeet)] at hc
    omega

end Mei.OrientedCell

namespace Mei.Convex.WallComplement

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {σ : ι → OrientedCell h 1}
  {x y : WallComplement (fun j => (σ j).carrier)}

/-- An admissible segment is a transverse affine one-simplex for every wall cell,
including cells that it misses. -/
theorem AdmissibleSegment.isTransverse_orientedCell (e : AdmissibleSegment x y) (j : ι) :
    (σ j).IsTransverse ![x.val, y.val] := by
  have hhull : convexHull ℝ (range ![x.val, y.val]) = segment ℝ x.val y.val := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair]
  have hmeet : (convexHull ℝ (range ![x.val, y.val]) ∩ (σ j).carrier).Nonempty ↔
      ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ (σ j).carrier := by
    rw [hhull, segment_eq_image_lineMap]
    exact Set.image_inter_nonempty_iff
  refine ⟨?_, fun hm => ?_⟩
  · rw [hhull, segment_eq_image_lineMap]
    refine disjoint_left.mpr ?_
    rintro z ⟨t, ht, rfl⟩ hz
    exact e.regular t ht (mem_singularSupport.mpr (Or.inl ⟨j, hz⟩))
  · rw [linearIndependent_unique_iff]
    simpa only [Function.comp_apply, Fin.default_eq_zero, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_zero, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_sub, ne_eq, Submodule.Quotient.mk_eq_zero] using
      e.transverse j (hmeet.mp hm)

open Classical in
/-- The geometric intersection index is the negative crossing exponent for left
wall actions. The coorientation need only induce the cell's orientation. -/
theorem intersectionIndex_eq_neg_crossingExponent (e : AdmissibleSegment x y)
    (ν : V →ₗ[ℝ] ℝ) (j : ι)
    (hν : ∀ v : V, SignType.sign (ν v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v)) :
    (σ j).intersectionIndex ![x.val, y.val] =
      -(if ∃ t, (j, t) ∈ crossings x y then
        (if 0 < ν (y.val - x.val) then -1 else 1 : ℤ) else 0) := by
  have hm : (convexHull ℝ (range ![x.val, y.val]) ∩ (σ j).carrier).Nonempty ↔
      ∃ t, (j, t) ∈ crossings x y := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair, segment_eq_image_lineMap]
    simp only [mem_crossings]
    exact Set.image_inter_nonempty_iff
  by_cases hc : ∃ t, (j, t) ∈ crossings x y
  · rw [OrientedCell.intersectionIndex_of_nonempty (hm.mpr hc), ite_eq_left hc]
    have hframe : (fun j : Fin 1 => ![x.val, y.val] j.succ - ![x.val, y.val] 0) =
        fun _ : Fin 1 => y.val - x.val := by ext j; fin_cases j; rfl
    rw [hframe, ← hν]
    have hn : ν (y.val - x.val) ≠ 0 := by
      intro hz
      have hs := (e.isTransverse_orientedCell j).intersectionIndex_eq_zero_iff
      have hi : (σ j).intersectionIndex ![x.val, y.val] = 0 := by
        rw [OrientedCell.intersectionIndex_of_nonempty (hm.mpr hc), hframe, ← hν, hz]
        simp
      exact (hm.mpr hc).not_disjoint (hs.mp hi)
    rcases lt_or_gt_of_ne hn with hn | hn
    · simp only [sign_neg hn, SignType.coe_neg_one, ite_eq_right (not_lt.mpr hn.le)]
    · simp only [sign_pos hn, SignType.coe_one, ite_eq_left hn]
      norm_num
  · rw [OrientedCell.intersectionIndex_of_disjoint
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp (hm.not.mpr hc))),
      ite_eq_right hc, neg_zero]

variable [Fintype ι] {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- A segment crossing exactly one indexed cell extracts its coefficient with
the orientation sign. No bound on the length of the segment is required. -/
theorem intersectionPairing_eq_of_crossings_singleton
    (j : ι) (t : ℝ) (he : crossings x y = {(j, t)}) (c : ι → E) :
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (∑ a, Finsupp.single (σ a) (c a)) =
      ((σ j).orientation.evalSign (fun _ : Fin 1 => y.val - x.val) : ℤ) • c j := by
  classical
  have hmeet (a : ι) :
      (convexHull ℝ (range ![x.val, y.val]) ∩ (σ a).carrier).Nonempty ↔ a = j := by
    have hm : (convexHull ℝ (range ![x.val, y.val]) ∩ (σ a).carrier).Nonempty ↔
        ∃ u, (a, u) ∈ crossings x y := by
      rw [Matrix.range_cons_cons_empty, convexHull_pair, segment_eq_image_lineMap]
      simp only [mem_crossings]
      exact Set.image_inter_nonempty_iff
    rw [hm, he]
    simp
  rw [map_sum, Finset.sum_eq_single j]
  · rw [OrientedCell.intersectionPairing_single,
      OrientedCell.intersectionIndex_of_nonempty ((hmeet j).mpr rfl)]
    have hframe : (fun a : Fin 1 => ![x.val, y.val] a.succ - ![x.val, y.val] 0) =
        fun _ : Fin 1 => y.val - x.val := by ext a; fin_cases a; rfl
    rw [hframe]
  · intro a _ ha
    rw [OrientedCell.intersectionPairing_single,
      OrientedCell.intersectionIndex_of_disjoint
        (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp
          ((hmeet a).not.mpr ha))), zero_smul]
  · simp

/-- Pairing a segment with an indexed finite wall presentation gives the negative
of its crossing sum. Repeated cells and simultaneous crossings are counted with
their original multiplicities. Zero-coefficient walls need no coorientation compatibility. -/
theorem intersectionPairing_eq_neg_wallCrossingSum (e : x ⟶ y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v)) :
    OrientedCell.intersectionPairing (R := R) ![x.val, y.val]
        (∑ j, Finsupp.single (σ j) (c j)) = -e.toPath.wallCrossingSum ν c := by
  classical
  have he := wallCrossingSum_toPath e ν c
  dsimp only at he
  -- The segment formula chooses a finite enumeration; the indexed presentation uses ours.
  rw [Subsingleton.elim (Fintype.ofFinite ι) (inferInstance : Fintype ι)] at he
  rw [he, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [OrientedCell.intersectionPairing_single]
  by_cases hc : c j = 0
  · simp [hc]
  · rw [intersectionIndex_eq_neg_crossingExponent e.down (ν j) j (hν j hc), neg_zsmul]

variable {κ : Type*} [Fintype κ] {τ : κ → OrientedCell h 1}
  {x' y' : WallComplement (fun j => (τ j).carrier)}

/-- Equal polyhedral cochains have equal additive transport on common admissible
segments. The presentations may differ by subdivision, orientation reversal,
or cancellation of coincident cells. -/
theorem wallCrossingSum_toPath_eq_of_cochain_eq
    (e : x ⟶ y) (e' : x' ⟶ y')
    (ν : ι → V →ₗ[ℝ] ℝ) (μ : κ → V →ₗ[ℝ] ℝ) (c : ι → E) (c' : κ → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hμ : ∀ j, c' j ≠ 0 → ∀ v, SignType.sign (μ j v) =
      (τ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : ∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j) =
      ∑ j, PolyhedralCochain.mk (τ j) (c' j))
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    e.toPath.wallCrossingSum ν c = e'.toPath.wallCrossingSum μ c' := by
  classical
  have hf : PolyhedralCochain.ofFinsupp (R := R)
      (∑ j, Finsupp.single (σ j) (c j)) =
      PolyhedralCochain.ofFinsupp (∑ j, Finsupp.single (τ j) (c' j)) := by
    simpa only [map_sum, PolyhedralCochain.ofFinsupp_single] using hc
  have ht {a b : WallComplement (fun j => (σ j).carrier)} (f : a ⟶ b)
      (υ : OrientedCell h 1) (hυ : υ ∈ (∑ j, Finsupp.single (σ j) (c j)).support) :
      υ.IsTransverse ![a.val, b.val] := by
    obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum υ hυ
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hj
    exact f.down.isTransverse_orientedCell j
  have ht' (υ : OrientedCell h 1)
      (hυ : υ ∈ (∑ j, Finsupp.single (τ j) (c' j)).support) :
      υ.IsTransverse ![x.val, y.val] := by
    obtain ⟨j, _, hj⟩ := Finsupp.mem_support_finsetSum υ hυ
    obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hj
    simpa only [hx, hy] using e'.down.isTransverse_orientedCell j
  have he := PolyhedralCochain.intersectionPairing_eq_of_ofFinsupp_eq
    (v := ![x.val, y.val]) hf (ht e) ht'
  conv_rhs at he => rw [hx, hy]
  rw [intersectionPairing_eq_neg_wallCrossingSum e ν c hν,
    intersectionPairing_eq_neg_wallCrossingSum e' μ c' hμ] at he
  exact neg_injective he

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Fintype ι]
  {σ : ι → OrientedCell h 1}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]
  {x y : WallComplement (fun j => (σ j).carrier)}

/-- Summing the segment intersection pairings along a polygonal path gives the
negative additive crossing sum, retaining repeated visits to each wall. -/
theorem addWeightOfEPs_intersectionPairing_eq_neg_wallCrossingSum (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v)) :
    p.addWeightOfEPs (fun a b => OrientedCell.intersectionPairing (R := R)
      ![a.val, b.val] (∑ j, Finsupp.single (σ j) (c j))) = -p.wallCrossingSum ν c := by
  induction p with
  | nil => simp [addWeightOfEPs_nil]
  | cons p e ih =>
    rw [addWeightOfEPs_cons, ih, intersectionPairing_eq_neg_wallCrossingSum e ν c hν,
      ← comp_toPath_eq_cons, wallCrossingSum_comp, neg_add]

section Comparison

variable {κ : Type*} [Fintype κ] {τ : κ → OrientedCell h 1}
  {x' y' : WallComplement (fun j => (τ j).carrier)}

/-- Equal cochains give equal crossing sums along any common polygonal vertex
list. No common subdivision of the wall presentations needs to be chosen. -/
theorem wallCrossingSum_eq_of_cochain_eq
    {W : ι → Set V} {W' : κ → Set V}
    {a b : WallComplement W} {a' b' : WallComplement W'}
    (p : AdmissiblePLPath a b) (q : AdmissiblePLPath a' b')
    (ν : ι → V →ₗ[ℝ] ℝ) (μ : κ → V →ₗ[ℝ] ℝ) (c : ι → E) (c' : κ → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hμ : ∀ j, c' j ≠ 0 → ∀ v, SignType.sign (μ j v) =
      (τ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : ∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j) =
      ∑ j, PolyhedralCochain.mk (τ j) (c' j))
    (hσ : ∀ j, (σ j).carrier = W j) (hτ : ∀ j, (τ j).carrier = W' j)
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    p.wallCrossingSum ν c = q.wallCrossingSum μ c' := by
  obtain rfl : W = fun j => (σ j).carrier := (funext hσ).symm
  obtain rfl : W' = fun j => (τ j).carrier := (funext hτ).symm
  induction p generalizing a' b' with
  | nil =>
    cases q with
    | nil => simp
    | cons q e =>
      have he := congrArg List.length hpq
      simp only [List.length_map, vertices_length, length_nil, length_cons] at he
      omega
  | @cons z w p e ih =>
    cases q with
    | nil =>
      have he := congrArg List.length hpq
      simp only [List.length_map, vertices_length, length_nil, length_cons] at he
      omega
    | @cons z' w' q e' =>
      simp only [vertices_cons, List.map_concat, List.concat_inj] at hpq
      have hz : z.val = z'.val := by
        have he := congrArg List.getLast? hpq.1
        simpa [List.getLast?_eq_some_getLast, p.vertices_ne_nil, q.vertices_ne_nil] using he
      rw [← comp_toPath_eq_cons, ← comp_toPath_eq_cons, wallCrossingSum_comp,
        wallCrossingSum_comp, ih q hpq.1,
        wallCrossingSum_toPath_eq_of_cochain_eq e e' ν μ c c' hν hμ hc hz hpq.2]

end Comparison

/-- Cochain cancellation forces vanishing of additive transport along every
admissible path. This uses the actual cochain quotient, allowing orientation
relations and arbitrary subdivisions rather than only literal coefficient cancellation. -/
theorem wallCrossingSum_eq_zero_of_cochain_eq_zero (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (c : ι → E)
    (hν : ∀ j, c j ≠ 0 → ∀ v, SignType.sign (ν j v) =
      (σ j).orientation.evalSign (fun _ : Fin 1 => v))
    (hc : ∑ j, PolyhedralCochain.mk (R := R) (σ j) (c j) = 0) :
    p.wallCrossingSum ν c = 0 := by
  have he := p.wallCrossingSum_eq_of_cochain_eq (R := R) p ν ν c (fun _ => 0)
    hν (by simp) (by simpa only [map_zero, Finset.sum_const_zero] using hc)
    (fun _ => rfl) (fun _ => rfl) rfl
  simpa [wallCrossingSum_def] using he

end Quiver.Path
