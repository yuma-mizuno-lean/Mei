/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Enumeration
import Mei.Geometry.Convex.Polyhedron.Path.Hyperplane

/-!
# The local segment cocycle

Segment transport through a finite family of closed walls satisfies the cocycle
identity `P_{yz} P_{xy} = P_{xz}` whenever the filled triangle with vertices `x, y, z`
misses the singular support. No commutation is assumed between labels of walls with
different affine spans, and the triangle may meet arbitrarily many walls.

On a convex set `K` missing the singular support, each closed wall meeting `K` agrees
there with its affine span: its intersection with `K` is relatively clopen in the convex
set `K ∩ affineSpan`. Hence two walls cannot cross inside `K` unless they have the same
affine span. In the triangle, each crossed wall separates one vertex from the other
two. Walls separating a common vertex are crossed in the same order along both edges
at that vertex, and they are crossed before the walls separating the opposite edge's
endpoints. Comparing time-sorted enumerations of the crossed walls on the three edges
(`WallComplement.segmentPathProduct_eq_prod_of_pairwise`) then gives the identity.

Segments between off-wall points of such a convex set are automatically admissible.
These facts make segment transport a locally constant cocycle on the complement of the
singular support, the input for coefficient local systems of wall diagrams; compare
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
[arXiv:1601.07081](https://arxiv.org/abs/1601.07081), §3.2.
-/

public section

noncomputable section

open Set Topology Mei.Convex Mei.Convex.WallComplement

namespace Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V} {K : Set V}

/-- On a convex set missing the singular support of a wall family, a closed wall meeting
the set contains every point of the set lying in the wall's affine span. -/
theorem inter_affineSpan_subset_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι} (hclosed : IsClosed (W j))
    (hmeet : (K ∩ W j).Nonempty) : K ∩ affineSpan ℝ (W j) ⊆ W j := by
  set S := K ∩ (affineSpan ℝ (W j) : Set V)
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (hK.inter (affineSpan ℝ (W j)).convex).isPreconnected
  -- The points of the wall form a clopen subset of the connected set `S`.
  let Z : Set S := {v | (v : V) ∈ W j}
  have hZ : IsClopen Z := by
    refine ⟨hclosed.preimage continuous_subtype_val, isOpen_iff_mem_nhds.mpr fun v hv => ?_⟩
    rw [mem_nhds_subtype_iff_nhdsWithin]
    have hint := mem_intrinsicInterior_of_notMem_singularSupport (W := W) (i := j)
      (x := (v : V)) hv (hKW.notMem_of_mem_left v.2.1)
    filter_upwards [nhdsWithin_mono _ inter_subset_right
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hint),
      self_mem_nhdsWithin] with w hw hwS
    exact ⟨⟨w, hwS⟩, hw, rfl⟩
  obtain ⟨p, hpK, hpW⟩ := hmeet
  have huniv := hZ.eq_univ ⟨⟨p, hpK, subset_affineSpan ℝ _ hpW⟩, hpW⟩
  intro v hv
  have hvZ : (⟨v, hv⟩ : S) ∈ Z := huniv ▸ mem_univ _
  exact hvZ

/-- On a convex set missing the singular support, a closed wall meeting the set at `p`
consists there of the points where a normal of its affine span takes its value at `p`. -/
theorem mem_iff_apply_eq_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι} (hclosed : IsClosed (W j))
    {ν : V →ₗ[ℝ] ℝ} (hν : LinearMap.ker ν = (affineSpan ℝ (W j)).direction)
    {p : V} (hpK : p ∈ K) (hpW : p ∈ W j) {v : V} (hv : v ∈ K) :
    v ∈ W j ↔ ν v = ν p := by
  have hp : p ∈ affineSpan ℝ (W j) := subset_affineSpan ℝ _ hpW
  have hiff : v ∈ affineSpan ℝ (W j) ↔ ν v = ν p := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp, ← hν, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, sub_eq_zero]
  refine ⟨fun h => hiff.mp (subset_affineSpan ℝ _ h), fun h => ?_⟩
  exact hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW hclosed ⟨p, hpK, hpW⟩
    ⟨hv, hiff.mpr h⟩

/-- On a convex set missing the singular support, two closed walls with a common point
in the set agree on the set. -/
theorem mem_iff_mem_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j k : ι} (hj : IsClosed (W j)) (hk : IsClosed (W k))
    {p : V} (hpK : p ∈ K) (hpj : p ∈ W j) (hpk : p ∈ W k) {v : V} (hv : v ∈ K) :
    v ∈ W j ↔ v ∈ W k := by
  have hdir : (affineSpan ℝ (W j)).direction = (affineSpan ℝ (W k)).direction := by
    by_contra hne
    exact hKW.notMem_of_mem_left hpK (mem_singularSupport.mpr (Or.inr ⟨j, k, hne, hpj, hpk⟩))
  have hspan := AffineSubspace.ext_of_direction_eq hdir
    ⟨p, subset_affineSpan ℝ _ hpj, subset_affineSpan ℝ _ hpk⟩
  have hsub {i : ι} (hi : IsClosed (W i)) (hpi : p ∈ W i) :
      v ∈ W i ↔ v ∈ affineSpan ℝ (W i) :=
    ⟨fun h => subset_affineSpan ℝ _ h, fun h =>
      hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW hi ⟨p, hpK, hpi⟩ ⟨hv, h⟩⟩
  rw [hsub hj hpj, hsub hk hpk, hspan]

/-- Two closed walls do not cross inside a convex set missing the singular support: the
normal of one wall does not change sign between two points of another wall in the set. -/
theorem sub_mul_sub_nonneg_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j k : ι} (hj : IsClosed (W j)) (hk : IsClosed (W k))
    {ν : V →ₗ[ℝ] ℝ} (hν : LinearMap.ker ν = (affineSpan ℝ (W k)).direction)
    {p q r : V} (hpK : p ∈ K) (hpW : p ∈ W j) (hqK : q ∈ K) (hqW : q ∈ W j)
    (hrK : r ∈ K) (hrW : r ∈ W k) :
    0 ≤ (ν p - ν r) * (ν q - ν r) := by
  refine le_of_not_gt fun hneg => ?_
  set a := ν p - ν r
  set b := ν q - ν r
  have hab : a - b ≠ 0 := fun h => by
    rw [sub_eq_zero.mp h] at hneg
    nlinarith [mul_self_nonneg b]
  -- The zero of the normal along the segment from `p` to `q`.
  set t := a / (a - b)
  set m := AffineMap.lineMap p q t
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne hab with h | h
    · constructor
      · exact div_nonneg_of_nonpos (by nlinarith) h.le
      · rw [div_le_one_of_neg h]; nlinarith
    · constructor
      · exact div_nonneg (by nlinarith) h.le
      · rw [div_le_one h]; nlinarith
  have hmK : m ∈ K := hK.lineMap_mem hpK hqK ht
  have hmj : m ∈ W j := hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW hj
    ⟨p, hpK, hpW⟩ ⟨hmK, AffineMap.lineMap_mem t (subset_affineSpan ℝ _ hpW)
      (subset_affineSpan ℝ _ hqW)⟩
  have hνm : ν m = ν r := by
    have hm : ν m = (1 - t) * ν p + t * ν q := by
      simp only [m, AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
    have htab : t * (a - b) = a := div_mul_cancel₀ a hab
    rw [hm]
    linear_combination (-1 : ℝ) * htab
  have hmk : m ∈ W k :=
    (hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW hk hν hrK hrW hmK).mpr hνm
  have hpk : p ∈ W k := (hK.mem_iff_mem_of_disjoint_singularSupport hKW hj hk hmK hmj hmk
    hpK).mp hpW
  have ha : a = 0 := sub_eq_zero.mpr
    ((hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW hk hν hrK hrW hpK).mp hpk)
  rw [ha, zero_mul] at hneg
  exact lt_irrefl _ hneg

/-- A segment between off-wall points of a convex set missing the singular support of a
closed wall family is admissible. -/
theorem admissibleSegment_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W))
    (hclosed : ∀ i, IsClosed (W i)) {x y : WallComplement W} (hx : x.val ∈ K)
    (hy : y.val ∈ K) : AdmissibleSegment x y where
  transverse i := by
    rintro ⟨t, ht, hti⟩ hd
    have hmeet : (K ∩ W i).Nonempty := ⟨_, hK.lineMap_mem hx hy ht, hti⟩
    apply x.notMem i
    apply hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW (hclosed i) hmeet
    refine ⟨hx, ?_⟩
    have hx' : x.val = (-t) • (y.val - x.val) +ᵥ AffineMap.lineMap x.val y.val t := by
      simp only [AffineMap.lineMap_apply_module, vadd_eq_add]
      module
    rw [hx']
    exact AffineSubspace.vadd_mem_of_mem_direction
      ((affineSpan ℝ (W i)).direction.smul_mem _ hd) (subset_affineSpan ℝ _ hti)
  regular t ht := hKW.notMem_of_mem_left (hK.lineMap_mem hx hy ht)

variable (hclosed : ∀ i, IsClosed (W i)) {ν : ι → V →ₗ[ℝ] ℝ}
  (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)

/-- Along a segment through a hyperplane `ν = c` at parameter `s`, the value of `ν - c` at
parameter `r`, scaled by `s`, is its value at the start scaled by `s - r`. -/
private theorem apply_lineMap_sub_mul (μ : V →ₗ[ℝ] ℝ) {u v : V} {s c : ℝ}
    (hs : μ (AffineMap.lineMap u v s) = c) (r : ℝ) :
    (μ (AffineMap.lineMap u v r) - c) * s = (μ u - c) * (s - r) := by
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul] at hs ⊢
  rw [← hs]
  ring

/-- Along a segment from `u` meeting the hyperplane `μ = c` at parameter `s > 0`, with
`u` off the hyperplane, points before `s` lie on the side of `u`. -/
private theorem mul_pos_of_lt_of_apply_lineMap (μ : V →ₗ[ℝ] ℝ) {u v : V} {s c r : ℝ}
    (hs : μ (AffineMap.lineMap u v s) = c) (hs0 : 0 < s) (hu : μ u - c ≠ 0) (hr : r < s) :
    0 < (μ (AffineMap.lineMap u v r) - c) * (μ u - c) := by
  have h := apply_lineMap_sub_mul μ hs r
  have : 0 < (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s := by
    rw [show (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s =
      (μ u - c) * (μ u - c) * (s - r) by linear_combination (μ u - c) * h]
    exact mul_pos (mul_self_pos.mpr hu) (by linarith)
  exact pos_of_mul_pos_left this hs0.le

/-- Along a segment from `u` meeting the hyperplane `μ = c` at parameter `s > 0`, with
`u` off the hyperplane, points after `s` lie on the side opposite to `u`. -/
private theorem mul_neg_of_lt_of_apply_lineMap (μ : V →ₗ[ℝ] ℝ) {u v : V} {s c r : ℝ}
    (hs : μ (AffineMap.lineMap u v s) = c) (hs0 : 0 < s) (hu : μ u - c ≠ 0) (hr : s < r) :
    (μ (AffineMap.lineMap u v r) - c) * (μ u - c) < 0 := by
  have h := apply_lineMap_sub_mul μ hs r
  have : (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s < 0 := by
    rw [show (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s =
      (μ u - c) * (μ u - c) * (s - r) by linear_combination (μ u - c) * h]
    exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hu) (by linarith)
  by_contra hneg
  exact this.not_ge (mul_nonneg (not_lt.mp hneg) hs0.le)

include hclosed hν in
/-- A segment between points of `K` crosses a wall meeting `K` at `p` exactly when its
endpoints lie on opposite sides of the hyperplane through `p`. The crossing exponent is
then determined by the side of the target. -/
private theorem exists_crossing_iff_of_mem (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι} {p : V} (hpK : p ∈ K) (hpW : p ∈ W j)
    (u v : WallComplement W) (hu : u.val ∈ K) (hv : v.val ∈ K) :
    ((∃ t, (j, t) ∈ crossings u v) ↔ ((0 < ν j u.val - ν j p) ≠ (0 < ν j v.val - ν j p))) ∧
      ((∃ t, (j, t) ∈ crossings u v) →
        (0 < ν j (v.val - u.val) ↔ 0 < ν j v.val - ν j p)) := by
  have hiff : (∃ t, (j, t) ∈ crossings u v) ↔
      ((0 < ν j u.val - ν j p) ≠ (0 < ν j v.val - ν j p)) := by
    have := exists_crossing_iff_of_hyperplane u v
      ((ν j).toAffineMap - AffineMap.const ℝ V (ν j p)) (j := j) fun w hw => by
        simp only [AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
          AffineMap.const_apply, sub_eq_zero]
        exact hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hclosed j) (hν j) hpK hpW
          (hK.segment_subset hu hv hw)
    simpa only [AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
      AffineMap.const_apply]
      using this
  refine ⟨hiff, fun h => ?_⟩
  have hs := hiff.mp h
  rw [map_sub]
  constructor
  · intro hd
    by_contra hv'
    exact hs (propext ⟨fun _ => absurd (by linarith : 0 < ν j v.val - ν j p) hv',
      fun h' => absurd h' hv'⟩)
  · intro hv'
    by_contra hd
    exact hs (propext ⟨fun _ => hv', fun _ => by linarith⟩)

include hclosed hν in
/-- Walls separating a vertex `a` from `b` and `c` are crossed in the same order along
the edges `[a, b]` and `[a, c]`. -/
private theorem crossing_le_of_crossing_le (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {a b c : WallComplement W} (ha : a.val ∈ K)
    (hb : b.val ∈ K) (hc : c.val ∈ K) {j k : ι} {s s' t t' : ℝ}
    (hjs : (j, s) ∈ crossings a b) (hks : (k, s') ∈ crossings a b)
    (hjt : (j, t) ∈ crossings a c) (hkt : (k, t') ∈ crossings a c) (hss : s ≤ s') :
    t ≤ t' := by
  refine le_of_not_gt fun htt => ?_
  obtain ⟨hsI, hjs⟩ := (mem_crossings _ _ _ _).mp hjs
  obtain ⟨hs'I, hks⟩ := (mem_crossings _ _ _ _).mp hks
  obtain ⟨htI, hjt⟩ := (mem_crossings _ _ _ _).mp hjt
  obtain ⟨ht'I, hkt⟩ := (mem_crossings _ _ _ _).mp hkt
  have hpK := hK.lineMap_mem ha hb hsI
  have hpkK := hK.lineMap_mem ha hb hs'I
  have hqK := hK.lineMap_mem ha hc htI
  have hmem := fun {v : V} (hv : v ∈ K) =>
    hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hclosed k) (hν k) hpkK hks hv
  obtain ⟨d, hd⟩ : ∃ d, ν k (AffineMap.lineMap a.val b.val s') = d := ⟨_, rfl⟩
  rw [hd] at hmem
  have hda : ν k a.val - d ≠ 0 := fun h => a.notMem k ((hmem ha).mpr (sub_eq_zero.mp h))
  have hqk : ν k (AffineMap.lineMap a.val c.val t') = d :=
    (hmem (hK.lineMap_mem ha hc ht'I)).mp hkt
  have h₂ := apply_lineMap_sub_mul (ν k) hqk t
  have ht' : 0 < t' := by
    rcases ht'I.1.lt_or_eq with h | h
    · exact h
    · rw [← h, AffineMap.lineMap_apply_zero] at hkt
      exact absurd hkt (a.notMem k)
  rcases hss.lt_or_eq with hss | rfl
  · -- Strictly earlier along `[a, b]`: wall `k` separates the two crossings of wall `j`.
    have hsign₁ := mul_pos_of_lt_of_apply_lineMap (ν k) hd (lt_of_le_of_lt hsI.1 hss) hda hss
    have hsign₂ := mul_neg_of_lt_of_apply_lineMap (ν k) hqk ht' hda htt
    refine (hK.sub_mul_sub_nonneg_of_disjoint_singularSupport hKW (hclosed j) (hclosed k)
      (hν k) hpK hjs hqK hjt hpkK hks).not_gt ?_
    rw [hd]
    nlinarith [mul_neg_of_pos_of_neg hsign₁ hsign₂, mul_self_nonneg (ν k a.val - d)]
  · -- Simultaneous along `[a, b]`: the walls agree on `K`, so they cross `[a, c]` together.
    have hqk' : ν k (AffineMap.lineMap a.val c.val t) = d :=
      (hmem hqK).mp ((hK.mem_iff_mem_of_disjoint_singularSupport hKW (hclosed j) (hclosed k)
        hpK hjs hks hqK).mp hjt)
    rw [hqk', sub_self, zero_mul] at h₂
    rcases mul_eq_zero.mp h₂.symm with h | h
    · exact hda h
    · linarith

include hclosed hν in
/-- Along an edge `[a, b]`, a wall separating `a` from `b` and `c` is crossed no later
than a wall separating `b` from `a` and `c`. -/
private theorem crossing_le_of_crossing_opposite (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {a b c : WallComplement W} (ha : a.val ∈ K)
    (hb : b.val ∈ K) (hc : c.val ∈ K) {j k : ι} {s s' : ℝ}
    (hjs : (j, s) ∈ crossings a b) (hjc : ∃ t, (j, t) ∈ crossings a c)
    (hks : (k, s') ∈ crossings a b) (hkc : ∃ u, (k, u) ∈ crossings b c) : s ≤ s' := by
  refine le_of_not_gt fun hss => ?_
  obtain ⟨t, hjt⟩ := hjc
  obtain ⟨htI, hjt⟩ := (mem_crossings _ _ _ _).mp hjt
  obtain ⟨u, hku⟩ := hkc
  obtain ⟨huI, hku⟩ := (mem_crossings _ _ _ _).mp hku
  obtain ⟨hsI, hjs⟩ := (mem_crossings _ _ _ _).mp hjs
  obtain ⟨hs'I, hks⟩ := (mem_crossings _ _ _ _).mp hks
  have hpK := hK.lineMap_mem ha hb hsI
  have hpkK := hK.lineMap_mem ha hb hs'I
  have hrK := hK.lineMap_mem hb hc huI
  obtain ⟨d, hd⟩ : ∃ d, ν j (AffineMap.lineMap a.val b.val s) = d := ⟨_, rfl⟩
  have hmem {v : V} (hv : v ∈ K) : v ∈ W j ↔ ν j v = d := hd ▸
    hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hclosed j) (hν j) hpK hjs hv
  have hda : ν j a.val - d ≠ 0 := fun h => a.notMem j ((hmem ha).mpr (sub_eq_zero.mp h))
  have hs : 0 < s := lt_of_le_of_lt hs'I.1 hss
  have hqt : ν j (AffineMap.lineMap a.val c.val t) = d :=
    (hmem (hK.lineMap_mem ha hc htI)).mp hjt
  have ht : 0 < t := by
    rcases htI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, AffineMap.lineMap_apply_zero] at hjt
      exact absurd hjt (a.notMem j)
  have hbne : s < 1 := by
    rcases hsI.2.lt_or_eq with h | h
    · exact h
    · rw [h, AffineMap.lineMap_apply_one] at hjs
      exact absurd hjs (b.notMem j)
  have htne : t < 1 := by
    rcases htI.2.lt_or_eq with h | h
    · exact h
    · rw [h, AffineMap.lineMap_apply_one] at hjt
      exact absurd hjt (c.notMem j)
  -- Wall `j` puts `b` and `c` opposite to `a`, and the earlier crossing of `k` with `a`.
  have hb' := mul_neg_of_lt_of_apply_lineMap (ν j) hd hs hda hbne
  have hc' := mul_neg_of_lt_of_apply_lineMap (ν j) hqt ht hda htne
  rw [AffineMap.lineMap_apply_one] at hb' hc'
  have hp' := mul_pos_of_lt_of_apply_lineMap (ν j) hd hs hda hss
  have hr' : (ν j (AffineMap.lineMap b.val c.val u) - d) * (ν j a.val - d) < 0 := by
    have hr : ν j (AffineMap.lineMap b.val c.val u) - d =
        (1 - u) * (ν j b.val - d) + u * (ν j c.val - d) := by
      simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
      ring
    rw [hr, add_mul, mul_assoc, mul_assoc]
    rcases huI.1.lt_or_eq with hu | hu
    · exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr huI.2) hb'.le)
        (mul_neg_of_pos_of_neg hu hc')
    · rw [← hu, sub_zero, one_mul, zero_mul, add_zero]
      exact hb'
  refine (hK.sub_mul_sub_nonneg_of_disjoint_singularSupport hKW (hclosed k) (hclosed j) (hν j)
    hpkK hks hrK hku hpK hjs).not_gt (by
      rw [hd]
      nlinarith [mul_neg_of_pos_of_neg hp' hr', mul_self_nonneg (ν j a.val - d)])

/-- Propositional bookkeeping for a wall and a triangle: if crossings of the three edges are
side changes between the vertices and crossing exponents are read off at the targets, the
wall crosses exactly two edges or none, with matching exponents at the shared vertex. -/
private theorem classes_of_sides {P Q R α β γ sP sQ sR : Prop} (hP : P ↔ ¬(α ↔ β))
    (hQ : Q ↔ ¬(α ↔ γ)) (hR : R ↔ ¬(β ↔ γ)) (h₄ : P → (sP ↔ β)) (h₅ : Q → (sQ ↔ γ))
    (h₆ : R → (sR ↔ γ)) :
    (P ↔ (P ∧ Q) ∨ (P ∧ R)) ∧ (Q ↔ (P ∧ Q) ∨ (Q ∧ R)) ∧ (R ↔ (P ∧ R) ∨ (Q ∧ R)) ∧
      ¬(P ∧ Q ∧ R) ∧ (P → Q → (sP ↔ sQ)) ∧ (P → R → (sR ↔ ¬sP)) ∧
      (Q → R → (sR ↔ sQ)) := by
  rw [hP, hQ, hR] at *
  by_cases hα : α <;> by_cases hβ : β <;> by_cases hγ : γ <;> simp_all

include hclosed hν in
/-- Each wall crosses either no edge or exactly two edges of a triangle missing the singular
support, and its crossing exponents agree along the two edges at the vertex it separates,
with the exponent along the opposite edge reversed or preserved accordingly. -/
private theorem crossing_classes (hK : Convex ℝ K) (hKW : Disjoint K (singularSupport W))
    {x y z : WallComplement W} (hx : x.val ∈ K) (hy : y.val ∈ K) (hz : z.val ∈ K) (j : ι) :
    let P := ∃ t, (j, t) ∈ crossings x y
    let Q := ∃ t, (j, t) ∈ crossings x z
    let R := ∃ t, (j, t) ∈ crossings y z
    (P ↔ (P ∧ Q) ∨ (P ∧ R)) ∧ (Q ↔ (P ∧ Q) ∨ (Q ∧ R)) ∧ (R ↔ (P ∧ R) ∨ (Q ∧ R)) ∧
      ¬(P ∧ Q ∧ R) ∧ (P → Q → (0 < ν j (y.val - x.val) ↔ 0 < ν j (z.val - x.val))) ∧
      (P → R → (0 < ν j (z.val - y.val) ↔ ¬0 < ν j (y.val - x.val))) ∧
      (Q → R → (0 < ν j (z.val - y.val) ↔ 0 < ν j (z.val - x.val))) := by
  intro P Q R
  by_cases hmeet : (K ∩ W j).Nonempty
  · obtain ⟨p, hpK, hpW⟩ := hmeet
    have h := fun (u v : WallComplement W) (hu : u.val ∈ K) (hv : v.val ∈ K) =>
      exists_crossing_iff_of_mem hclosed hν hK hKW hpK hpW u v hu hv
    simp only [ne_eq, eq_iff_iff] at h
    exact classes_of_sides (h x y hx hy).1 (h x z hx hz).1 (h y z hy hz).1 (h x y hx hy).2
      (h x z hx hz).2 (h y z hy hz).2
  · have hno (u v : WallComplement W) (hu : u.val ∈ K) (hv : v.val ∈ K) :
        ¬∃ t, (j, t) ∈ crossings u v := fun ⟨t, ht⟩ =>
      hmeet ⟨_, hK.lineMap_mem hu hv ((mem_crossings _ _ _ _).mp ht).1,
        ((mem_crossings _ _ _ _).mp ht).2⟩
    exact classes_of_sides (α := True) (β := True) (γ := True)
      (iff_of_false (hno x y hx hy) (by simp)) (iff_of_false (hno x z hx hz) (by simp))
      (iff_of_false (hno y z hy hz) (by simp)) (fun h => (hno x y hx hy h).elim)
      (fun h => (hno x z hx hz h).elim) (fun h => (hno y z hy hz h).elim)

end Convex

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}
  (hclosed : ∀ i, IsClosed (W i)) {ν : ι → V →ₗ[ℝ] ℝ}
  (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)

variable [Finite ι] {G : Type*} [Group G] (ν) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))

include hclosed hν in
/-- **Local segment cocycle.** If the filled triangle with vertices `x, y, z` misses the
singular support of a finite family of closed walls, transport along `[x, y]` followed by
`[y, z]` equals transport along `[x, z]`. Labels of walls with different affine spans
need not commute, and the triangle may meet any number of walls. -/
theorem segmentPathProduct_mul_segmentPathProduct {x y z : WallComplement W}
    (hT : Disjoint (convexHull ℝ {x.val, y.val, z.val}) (singularSupport W))
    (e₁ : x ⟶ y) (e₂ : y ⟶ z) (e₃ : x ⟶ z) :
    segmentPathProduct ν label hcomm e₂ * segmentPathProduct ν label hcomm e₁ =
      segmentPathProduct ν label hcomm e₃ := by
  classical
  have := Fintype.ofFinite ι
  set K := convexHull ℝ {x.val, y.val, z.val}
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have hx : x.val ∈ K := subset_convexHull ℝ _ (by simp)
  have hy : y.val ∈ K := subset_convexHull ℝ _ (by simp)
  have hz : z.val ∈ K := subset_convexHull ℝ _ (by simp)
  -- Classes of walls by the vertex they separate from the opposite edge.
  let A := Finset.univ.filter fun j => (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings x z
  let B := Finset.univ.filter fun j => (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings y z
  let C := Finset.univ.filter fun j => (∃ t, (j, t) ∈ crossings x z) ∧ ∃ t, (j, t) ∈ crossings y z
  have hcl := fun j => Convex.crossing_classes hclosed hν hK hT hx hy hz j
  have hxy (j : ι) : (∃ t, (j, t) ∈ crossings x y) ↔ j ∈ A ∨ j ∈ B := by
    simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).1
  have hxz (j : ι) : (∃ t, (j, t) ∈ crossings x z) ↔ j ∈ A ∨ j ∈ C := by
    simpa only [A, C, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).2.1
  have hyz (j : ι) : (∃ t, (j, t) ∈ crossings y z) ↔ j ∈ B ∨ j ∈ C := by
    simpa only [B, C, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).2.2.1
  have hnot (j : ι) := (hcl j).2.2.2.1
  have hA (j : ι) (hj : j ∈ A) : (0 < ν j (y.val - x.val) ↔ 0 < ν j (z.val - x.val)) := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).2.2.2.2.1 hj.1 hj.2
  have hB (j : ι) (hj : j ∈ B) : (0 < ν j (z.val - y.val) ↔ ¬0 < ν j (y.val - x.val)) := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).2.2.2.2.2.1 hj.1 hj.2
  have hC (j : ι) (hj : j ∈ C) : (0 < ν j (z.val - y.val) ↔ 0 < ν j (z.val - x.val)) := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).2.2.2.2.2.2 hj.1 hj.2
  -- Crossing times along the two edges at `x`, used to sort the classes.
  let τ (u v : WallComplement W) (j : ι) : ℝ :=
    if h : ∃ t, (j, t) ∈ crossings u v then h.choose else 0
  have hτ {u v : WallComplement W} {j : ι} (h : ∃ t, (j, t) ∈ crossings u v) :
      (j, τ u v j) ∈ crossings u v := by
    simpa only [τ, h, dite_true] using h.choose_spec
  have hτeq {u v : WallComplement W} (e : u ⟶ v) {j : ι} {t : ℝ}
      (ht : (j, t) ∈ crossings u v) : t = τ u v j :=
    e.down.subsingleton_crossing j ((mem_crossings _ _ _ _).mp ht)
      ((mem_crossings _ _ _ _).mp (hτ ⟨t, ht⟩))
  have hsort (S : Finset ι) (f : ι → ℝ) : ∃ l : List ι, l.Nodup ∧ (∀ j, j ∈ l ↔ j ∈ S) ∧
      l.Pairwise fun j k => f j ≤ f k := by
    let r : ι → ι → Bool := fun j k => decide (f j ≤ f k)
    have hr := List.pairwise_mergeSort (le := r)
      (fun a b c hab hbc => by
        simp only [r, decide_eq_true_eq] at hab hbc ⊢
        exact hab.trans hbc)
      (fun a b => by simpa [r] using le_total (f a) (f b)) S.toList
    refine ⟨S.toList.mergeSort r, (List.mergeSort_perm _ _).nodup_iff.mpr S.nodup_toList,
      fun j => by simp, hr.imp fun h => ?_⟩
    simpa [r] using h
  obtain ⟨lA, hlA, hmA, hpA⟩ := hsort A (τ x y)
  obtain ⟨lB, hlB, hmB, hpB⟩ := hsort B (τ x y)
  obtain ⟨lC, hlC, hmC, hpC⟩ := hsort C (τ x z)
  have hAmem {j : ι} (hj : j ∈ A) :
      (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings x z := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hBmem {j : ι} (hj : j ∈ B) :
      (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings y z := by
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hCmem {j : ι} (hj : j ∈ C) :
      (∃ t, (j, t) ∈ crossings x z) ∧ ∃ t, (j, t) ∈ crossings y z := by
    simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hswap {u v : WallComplement W} {j : ι} (h : ∃ t, (j, t) ∈ crossings u v) :
      ∃ t, (j, t) ∈ crossings v u := by
    obtain ⟨t, ht⟩ := h
    exact ⟨1 - t, (mem_crossings_swap u v j (1 - t)).mpr (by simpa only [sub_sub_cancel])⟩
  have hswap' {u v : WallComplement W} {j : ι} {t : ℝ} (h : (j, t) ∈ crossings u v) :
      (j, 1 - t) ∈ crossings v u :=
    (mem_crossings_swap u v j (1 - t)).mpr (by simpa only [sub_sub_cancel])
  -- Transport along `[x, y]`: walls separating `x` precede walls separating `y`.
  have h₁ := segmentPathProduct_eq_prod_of_pairwise ν label hcomm e₁ (lA ++ lB)
    (List.nodup_append.mpr ⟨hlA, hlB, fun j hj k hk hjk => by
      subst hjk
      exact hnot j ⟨(hAmem ((hmA j).mp hj)).1, (hAmem ((hmA j).mp hj)).2,
        (hBmem ((hmB j).mp hk)).2⟩⟩)
    (fun j => by rw [List.mem_append, hmA, hmB, hxy])
    (List.pairwise_append.mpr ⟨hpA.imp fun h s t hs ht => (hτeq e₁ hs) ▸ (hτeq e₁ ht) ▸ h,
      hpB.imp fun h s t hs ht => (hτeq e₁ hs) ▸ (hτeq e₁ ht) ▸ h,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hclosed hν hK hT hx hy hz hs
        (hAmem ((hmA j).mp hj)).2 ht (hBmem ((hmB k).mp hk)).2⟩)
  -- Transport along `[x, z]`: walls separating `x` precede walls separating `z`.
  have h₃ := segmentPathProduct_eq_prod_of_pairwise ν label hcomm e₃ (lA ++ lC)
    (List.nodup_append.mpr ⟨hlA, hlC, fun j hj k hk hjk => by
      subst hjk
      exact hnot j ⟨(hAmem ((hmA j).mp hj)).1, (hAmem ((hmA j).mp hj)).2,
        (hCmem ((hmC j).mp hk)).2⟩⟩)
    (fun j => by rw [List.mem_append, hmA, hmC, hxz])
    (List.pairwise_append.mpr ⟨hpA.imp_of_mem fun {j k} hj hk h s t hs ht =>
        Convex.crossing_le_of_crossing_le hclosed hν hK hT hx hy hz
          (hτ (hAmem ((hmA j).mp hj)).1) (hτ (hAmem ((hmA k).mp hk)).1) hs ht h,
      hpC.imp fun h s t hs ht => (hτeq e₃ hs) ▸ (hτeq e₃ ht) ▸ h,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hclosed hν hK hT hx hz hy hs
        (hAmem ((hmA j).mp hj)).1 ht (hswap (hCmem ((hmC k).mp hk)).2)⟩)
  -- Transport along `[y, z]`: walls separating `y`, in reverse order, precede walls
  -- separating `z`.
  have h₂ := segmentPathProduct_eq_prod_of_pairwise ν label hcomm e₂ (lB.reverse ++ lC)
    (List.nodup_append.mpr ⟨List.nodup_reverse.mpr hlB, hlC, fun j hj k hk hjk => by
      subst hjk
      exact hnot j ⟨(hBmem ((hmB j).mp (List.mem_reverse.mp hj))).1,
        (hCmem ((hmC j).mp hk)).1, (hBmem ((hmB j).mp (List.mem_reverse.mp hj))).2⟩⟩)
    (fun j => by rw [List.mem_append, List.mem_reverse, hmB, hmC, hyz])
    (List.pairwise_append.mpr ⟨List.pairwise_reverse.mpr (hpB.imp_of_mem
        fun {j k} hj hk h s t hs ht =>
          Convex.crossing_le_of_crossing_le hclosed hν hK hT hy hx hz
          (hswap' (hτ (hBmem ((hmB k).mp hk)).1)) (hswap' (hτ (hBmem ((hmB j).mp hj)).1))
          hs ht (by linarith)),
      hpC.imp_of_mem fun {j k} hj hk h s t hs ht => by
        have := Convex.crossing_le_of_crossing_le hclosed hν hK hT hz hx hy
          (hswap' (hτ (hCmem ((hmC k).mp hk)).1)) (hswap' (hτ (hCmem ((hmC j).mp hj)).1))
          (hswap' ht) (hswap' hs) (by linarith)
        linarith,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hclosed hν hK hT hy hz hx hs
        (hswap (hBmem ((hmB j).mp (List.mem_reverse.mp hj))).1) ht
        (hswap (hCmem ((hmC k).mp hk)).1)⟩)
  -- Compare the signed labels class by class.
  have hgA : lA.reverse.map (fun j => label j ^ (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ)) =
      lA.reverse.map (fun j => label j ^ (if 0 < ν j (z.val - x.val) then -1 else 1 : ℤ)) :=
    List.map_congr_left fun j hj => by
      rw [if_congr (hA j ((hmA j).mp (List.mem_reverse.mp hj))) rfl rfl]
  have hgC : lC.reverse.map (fun j => label j ^ (if 0 < ν j (z.val - y.val) then -1 else 1 : ℤ)) =
      lC.reverse.map (fun j => label j ^ (if 0 < ν j (z.val - x.val) then -1 else 1 : ℤ)) :=
    List.map_congr_left fun j hj => by
      rw [if_congr (hC j ((hmC j).mp (List.mem_reverse.mp hj))) rfl rfl]
  have hgB : (lB.map fun j => label j ^ (if 0 < ν j (z.val - y.val) then -1 else 1 : ℤ)).prod =
      ((lB.reverse.map fun j =>
        label j ^ (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ)).prod)⁻¹ := by
    rw [List.prod_inv_reverse, List.map_map, List.map_reverse, List.reverse_reverse]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [if_congr (hB j ((hmB j).mp hj)) rfl rfl, Function.comp_apply]
    split_ifs <;> simp
  rw [h₁, h₂, h₃]
  simp only [List.reverse_append, List.reverse_reverse, List.map_append, List.prod_append]
  rw [hgA, hgC, hgB]
  group

end Mei.Convex.WallComplement
