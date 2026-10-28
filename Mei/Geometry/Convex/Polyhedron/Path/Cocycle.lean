/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Enumeration
import Mei.Geometry.Convex.Polyhedron.Path.Hyperplane
import Mei.LinearAlgebra.AffineSpace.Ordered
import Mei.Data.Finset.Sort

/-!
# The local segment cocycle

Segment transport through a finite family of walls satisfies the cocycle
identity `P_{yz} P_{xy} = P_{xz}` whenever the filled triangle with vertices `x, y, z`
misses the singular support. No commutation is assumed between labels of walls with
different affine spans, and the triangle may meet arbitrarily many walls.

On a convex set `K` missing the singular support, each wall meeting `K` agrees
there with its affine span: its intersection with `K` is relatively clopen in the convex
set `K ∩ affineSpan`. Hence two walls cannot cross inside `K` unless they have the same
affine span. In the triangle, each crossed wall separates one vertex from the other
two. Walls separating a common vertex are crossed in the same order along both edges
at that vertex, and they are crossed before the walls separating the opposite edge's
endpoints. Comparing time-sorted enumerations of the crossed walls on the three edges
(`WallComplement.segmentPathProduct_eq_prod_of_pairwise`) then gives the identity.

`Convex.admissibleSegment_of_disjoint_singularSupport` in the admissible-path module
supplies admissibility for segments between off-wall points of such a convex set.
The cocycle identity holds for off-wall endpoints in convex sets avoiding singular
support, providing compatibility needed to construct coefficient local systems of wall
diagrams; compare
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
[arXiv:1601.07081](https://arxiv.org/abs/1601.07081), §3.2.
-/

public section

noncomputable section

open Set Topology Mei.Convex Mei.Convex.WallComplement

namespace Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V} {K : Set V}

variable {ν : ι → V →ₗ[ℝ] ℝ}
  (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)

include hν in
/-- A segment between points of `K` crosses a wall meeting `K` at `p` exactly when its
endpoints lie on opposite sides of the hyperplane through `p`. The crossing exponent is
then determined by the side of the target. -/
private theorem exists_crossing_iff_of_mem (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι} {p : V} (hpK : p ∈ K) (hpW : p ∈ W j)
    (u v : WallComplement W) (hu : u.val ∈ K) (hv : v.val ∈ K) :
    ((∃ t, (j, t) ∈ crossings u v) ↔ (¬(0 < ν j u.val - ν j p ↔ 0 < ν j v.val - ν j p))) ∧
      ((∃ t, (j, t) ∈ crossings u v) →
        (0 < ν j (v.val - u.val) ↔ 0 < ν j v.val - ν j p)) := by
  have hiff : (∃ t, (j, t) ∈ crossings u v) ↔
      (¬(0 < ν j u.val - ν j p ↔ 0 < ν j v.val - ν j p)) := by
    have := exists_crossing_iff_of_hyperplane u v
      ((ν j).toAffineMap - AffineMap.const ℝ V (ν j p)) (j := j) fun w hw => by
        simp only [AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
          AffineMap.const_apply, sub_eq_zero]
        exact hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hν j) hpK hpW
          (hK.segment_subset hu hv hw)
    simpa only [AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
      AffineMap.const_apply, ne_eq, eq_iff_iff]
      using this
  refine ⟨hiff, fun h => ?_⟩
  have hs := hiff.mp h
  rw [map_sub]
  constructor
  · intro hd
    by_contra hv'
    exact hs ⟨fun _ => absurd (by linarith : 0 < ν j v.val - ν j p) hv',
      fun h' => absurd h' hv'⟩
  · intro hv'
    by_contra hd
    exact hs ⟨fun _ => hv', fun _ => by linarith⟩

include hν in
/-- Walls separating a vertex `a` from `b` and `c` are crossed in the same order along
the edges `[a, b]` and `[a, c]`. -/
private theorem crossing_le_of_crossing_le (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {a b c : WallComplement W} (ha : a.val ∈ K)
    (hb : b.val ∈ K) (hc : c.val ∈ K) {j k : ι} {s s' t t' : ℝ}
    (hjs : (j, s) ∈ crossings a b) (hks : (k, s') ∈ crossings a b)
    (hjt : (j, t) ∈ crossings a c) (hkt : (k, t') ∈ crossings a c) (hss : s ≤ s') :
    t ≤ t' := by
  refine le_of_not_gt fun htt => ?_
  have ht' := (mem_Ioo_of_mem_crossings hkt).1
  obtain ⟨hsI, hjs⟩ := (mem_crossings _ _ _ _).mp hjs
  obtain ⟨hs'I, hks⟩ := (mem_crossings _ _ _ _).mp hks
  obtain ⟨htI, hjt⟩ := (mem_crossings _ _ _ _).mp hjt
  obtain ⟨ht'I, hkt⟩ := (mem_crossings _ _ _ _).mp hkt
  have hpK := hK.lineMap_mem ha hb hsI
  have hpkK := hK.lineMap_mem ha hb hs'I
  have hqK := hK.lineMap_mem ha hc htI
  have hmem := fun {v : V} (hv : v ∈ K) =>
    hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hν k) hpkK hks hv
  obtain ⟨d, hd⟩ : ∃ d, ν k (AffineMap.lineMap a.val b.val s') = d := ⟨_, rfl⟩
  rw [hd] at hmem
  have hda : ν k a.val - d ≠ 0 := fun h => a.notMem k ((hmem ha).mpr (sub_eq_zero.mp h))
  have hqk : ν k (AffineMap.lineMap a.val c.val t') = d :=
    (hmem (hK.lineMap_mem ha hc ht'I)).mp hkt
  have h₂ := (ν k).apply_lineMap_sub_mul hqk t
  rcases hss.lt_or_eq with hss | rfl
  · -- Strictly earlier along `[a, b]`: wall `k` separates the two crossings of wall `j`.
    have hsign₁ := (ν k).mul_pos_of_lt_of_apply_lineMap hd (lt_of_le_of_lt hsI.1 hss) hda hss
    have hsign₂ := (ν k).mul_neg_of_lt_of_apply_lineMap hqk ht' hda htt
    refine (hK.sub_mul_sub_nonneg_of_disjoint_singularSupport hKW
      (hν k) hpK hjs hqK hjt hpkK hks).not_gt ?_
    rw [hd]
    nlinarith [mul_neg_of_pos_of_neg hsign₁ hsign₂, mul_self_nonneg (ν k a.val - d)]
  · -- Simultaneous along `[a, b]`: the walls agree on `K`, so they cross `[a, c]` together.
    have hqk' : ν k (AffineMap.lineMap a.val c.val t) = d :=
      (hmem hqK).mp ((hK.mem_iff_mem_of_disjoint_singularSupport hKW
        hpK hjs hks hqK).mp hjt)
    rw [hqk', sub_self, zero_mul] at h₂
    rcases mul_eq_zero.mp h₂.symm with h | h
    · exact hda h
    · linarith

include hν in
/-- Along an edge `[a, b]`, a wall separating `a` from `b` and `c` is crossed no later
than a wall separating `b` from `a` and `c`. -/
private theorem crossing_le_of_crossing_opposite (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {a b c : WallComplement W} (ha : a.val ∈ K)
    (hb : b.val ∈ K) (hc : c.val ∈ K) {j k : ι} {s s' : ℝ}
    (hjs : (j, s) ∈ crossings a b) (hjc : ∃ t, (j, t) ∈ crossings a c)
    (hks : (k, s') ∈ crossings a b) (hkc : ∃ u, (k, u) ∈ crossings b c) : s ≤ s' := by
  refine le_of_not_gt fun hss => ?_
  obtain ⟨t, hjt⟩ := hjc
  have ⟨ht, htne⟩ := mem_Ioo_of_mem_crossings hjt
  have hbne := (mem_Ioo_of_mem_crossings hjs).2
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
    hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW (hν j) hpK hjs hv
  have hda : ν j a.val - d ≠ 0 := fun h => a.notMem j ((hmem ha).mpr (sub_eq_zero.mp h))
  have hs : 0 < s := lt_of_le_of_lt hs'I.1 hss
  have hqt : ν j (AffineMap.lineMap a.val c.val t) = d :=
    (hmem (hK.lineMap_mem ha hc htI)).mp hjt
  -- Wall `j` puts `b` and `c` opposite to `a`, and the earlier crossing of `k` with `a`.
  have hb' := (ν j).mul_neg_of_lt_of_apply_lineMap hd hs hda hbne
  have hc' := (ν j).mul_neg_of_lt_of_apply_lineMap hqt ht hda htne
  rw [AffineMap.lineMap_apply_one] at hb' hc'
  have hp' := (ν j).mul_pos_of_lt_of_apply_lineMap hd hs hda hss
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
  refine (hK.sub_mul_sub_nonneg_of_disjoint_singularSupport hKW (hν j)
    hpkK hks hrK hku hpK hjs).not_gt (by
      rw [hd]
      nlinarith [mul_neg_of_pos_of_neg hp' hr', mul_self_nonneg (ν j a.val - d)])

/-- The edge classes and signs of one wall in a triangle. -/
private structure CrossingClasses (P Q R sP sQ sR : Prop) : Prop where
  xy_iff : P ↔ (P ∧ Q) ∨ (P ∧ R)
  xz_iff : Q ↔ (P ∧ Q) ∨ (Q ∧ R)
  yz_iff : R ↔ (P ∧ R) ∨ (Q ∧ R)
  not_all : ¬(P ∧ Q ∧ R)
  sign_at_x : P → Q → (sP ↔ sQ)
  sign_at_y : P → R → (sR ↔ ¬sP)
  sign_at_z : Q → R → (sR ↔ sQ)

/-- Propositional bookkeeping for a wall and a triangle: if crossings of the three edges are
side changes between the vertices and crossing exponents are read off at the targets, the
wall crosses exactly two edges or none, with matching exponents at the shared vertex. -/
private theorem classes_of_sides {P Q R α β γ sP sQ sR : Prop} (hP : P ↔ ¬(α ↔ β))
    (hQ : Q ↔ ¬(α ↔ γ)) (hR : R ↔ ¬(β ↔ γ)) (h₄ : P → (sP ↔ β)) (h₅ : Q → (sQ ↔ γ))
    (h₆ : R → (sR ↔ γ)) :
    CrossingClasses P Q R sP sQ sR := by
  rw [hP, hQ, hR] at *
  constructor <;>
    (by_cases hα : α <;> by_cases hβ : β <;> by_cases hγ : γ <;> simp_all)

include hν in
/-- Each wall crosses either no edge or exactly two edges of a triangle missing the singular
support, and its crossing exponents agree along the two edges at the vertex it separates,
with the exponent along the opposite edge reversed or preserved accordingly. -/
private theorem crossing_classes (hK : Convex ℝ K) (hKW : Disjoint K (singularSupport W))
    {x y z : WallComplement W} (hx : x.val ∈ K) (hy : y.val ∈ K) (hz : z.val ∈ K) (j : ι) :
    let P := ∃ t, (j, t) ∈ crossings x y
    let Q := ∃ t, (j, t) ∈ crossings x z
    let R := ∃ t, (j, t) ∈ crossings y z
    CrossingClasses P Q R (0 < ν j (y.val - x.val)) (0 < ν j (z.val - x.val))
      (0 < ν j (z.val - y.val)) := by
  intro P Q R
  by_cases hmeet : (K ∩ W j).Nonempty
  · obtain ⟨p, hpK, hpW⟩ := hmeet
    have h := fun (u v : WallComplement W) (hu : u.val ∈ K) (hv : v.val ∈ K) =>
      exists_crossing_iff_of_mem hν hK hKW hpK hpW u v hu hv
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
  {ν : ι → V →ₗ[ℝ] ℝ}
  (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)

variable [Finite ι] {G : Type*} [Group G] (ν) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))

include hν in
/-- **Local segment cocycle.** If the filled triangle with vertices `x, y, z` misses the
singular support of a finite family of walls, transport along `[x, y]` followed by
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
  have hcl := fun j => Convex.crossing_classes hν hK hT hx hy hz j
  have hxy (j : ι) : (∃ t, (j, t) ∈ crossings x y) ↔ j ∈ A ∨ j ∈ B := by
    simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).xy_iff
  have hxz (j : ι) : (∃ t, (j, t) ∈ crossings x z) ↔ j ∈ A ∨ j ∈ C := by
    simpa only [A, C, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).xz_iff
  have hyz (j : ι) : (∃ t, (j, t) ∈ crossings y z) ↔ j ∈ B ∨ j ∈ C := by
    simpa only [B, C, Finset.mem_filter, Finset.mem_univ, true_and] using (hcl j).yz_iff
  have hnot (j : ι) := (hcl j).not_all
  have hA (j : ι) (hj : j ∈ A) : (0 < ν j (y.val - x.val) ↔ 0 < ν j (z.val - x.val)) := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).sign_at_x hj.1 hj.2
  have hB (j : ι) (hj : j ∈ B) : (0 < ν j (z.val - y.val) ↔ ¬0 < ν j (y.val - x.val)) := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).sign_at_y hj.1 hj.2
  have hC (j : ι) (hj : j ∈ C) : (0 < ν j (z.val - y.val) ↔ 0 < ν j (z.val - x.val)) := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hcl j).sign_at_z hj.1 hj.2
  -- Sort each vertex class by crossing time along an edge at `x`.
  obtain ⟨lA, hlA, hmA, hpA⟩ := A.exists_nodup_pairwise_le_key (crossingTime x y)
  obtain ⟨lB, hlB, hmB, hpB⟩ := B.exists_nodup_pairwise_le_key (crossingTime x y)
  obtain ⟨lC, hlC, hmC, hpC⟩ := C.exists_nodup_pairwise_le_key (crossingTime x z)
  have hAmem {j : ι} (hj : j ∈ A) :
      (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings x z := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hBmem {j : ι} (hj : j ∈ B) :
      (∃ t, (j, t) ∈ crossings x y) ∧ ∃ t, (j, t) ∈ crossings y z := by
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hCmem {j : ι} (hj : j ∈ C) :
      (∃ t, (j, t) ∈ crossings x z) ∧ ∃ t, (j, t) ∈ crossings y z := by
    simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  -- Transport along `[x, y]`: walls separating `x` precede walls separating `y`.
  have h₁ := segmentPathProduct_eq_prod_of_pairwise ν label hcomm e₁ (lA ++ lB)
    (List.nodup_append.mpr ⟨hlA, hlB, fun j hj k hk hjk => by
      subst hjk
      exact hnot j ⟨(hAmem ((hmA j).mp hj)).1, (hAmem ((hmA j).mp hj)).2,
        (hBmem ((hmB j).mp hk)).2⟩⟩)
    (fun j => by rw [List.mem_append, hmA, hmB, hxy])
    (List.pairwise_append.mpr ⟨hpA.imp fun h s t hs ht =>
        (eq_crossingTime_of_mem e₁ hs) ▸ (eq_crossingTime_of_mem e₁ ht) ▸ h,
      hpB.imp fun h s t hs ht =>
        (eq_crossingTime_of_mem e₁ hs) ▸ (eq_crossingTime_of_mem e₁ ht) ▸ h,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hν hK hT hx hy hz hs
        (hAmem ((hmA j).mp hj)).2 ht (hBmem ((hmB k).mp hk)).2⟩)
  -- Transport along `[x, z]`: walls separating `x` precede walls separating `z`.
  have h₃ := segmentPathProduct_eq_prod_of_pairwise ν label hcomm e₃ (lA ++ lC)
    (List.nodup_append.mpr ⟨hlA, hlC, fun j hj k hk hjk => by
      subst hjk
      exact hnot j ⟨(hAmem ((hmA j).mp hj)).1, (hAmem ((hmA j).mp hj)).2,
        (hCmem ((hmC j).mp hk)).2⟩⟩)
    (fun j => by rw [List.mem_append, hmA, hmC, hxz])
    (List.pairwise_append.mpr ⟨hpA.imp_of_mem fun {j k} hj hk h s t hs ht =>
        Convex.crossing_le_of_crossing_le hν hK hT hx hy hz
          (mem_crossings_crossingTime (hAmem ((hmA j).mp hj)).1)
          (mem_crossings_crossingTime (hAmem ((hmA k).mp hk)).1) hs ht h,
      hpC.imp fun h s t hs ht =>
        (eq_crossingTime_of_mem e₃ hs) ▸ (eq_crossingTime_of_mem e₃ ht) ▸ h,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hν hK hT hx hz hy hs
        (hAmem ((hmA j).mp hj)).1 ht (exists_mem_crossings_swap.mpr (hCmem ((hmC k).mp hk)).2)⟩)
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
          Convex.crossing_le_of_crossing_le hν hK hT hy hx hz
          (mem_crossings_swap_of_mem (mem_crossings_crossingTime (hBmem ((hmB k).mp hk)).1))
          (mem_crossings_swap_of_mem (mem_crossings_crossingTime (hBmem ((hmB j).mp hj)).1))
          hs ht (by linarith)),
      hpC.imp_of_mem fun {j k} hj hk h s t hs ht => by
        have := Convex.crossing_le_of_crossing_le hν hK hT hz hx hy
          (mem_crossings_swap_of_mem (mem_crossings_crossingTime (hCmem ((hmC k).mp hk)).1))
          (mem_crossings_swap_of_mem (mem_crossings_crossingTime (hCmem ((hmC j).mp hj)).1))
          (mem_crossings_swap_of_mem ht) (mem_crossings_swap_of_mem hs) (by linarith)
        linarith,
      fun j hj k hk s t hs ht =>
        Convex.crossing_le_of_crossing_opposite hν hK hT hy hz hx hs
        (exists_mem_crossings_swap.mpr (hBmem ((hmB j).mp (List.mem_reverse.mp hj))).1) ht
        (exists_mem_crossings_swap.mpr (hCmem ((hmC k).mp hk)).1)⟩)
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
