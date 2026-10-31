/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Geometry.Affine.Segment

/-!
# Isolating simultaneous regular crossings

A short transverse segment through a point outside singular support meets exactly
the indexed walls through that point, all at its midpoint. Coincident walls retain
their distinct indices. In particular, every crossing event of an admissible segment is
the only event of a short admissible segment through its crossing point. A segment with
a single crossing event computes the unordered product of its signed wall labels, so no
enumeration of coincident walls is needed.

The geometric argument follows
`FinitePolyhedralComplex.eventually_exists_orderedCrossings_eq_singleton`,
with nonincident walls excluded by `IsClosed.isOpen_setOf_lineMap_notMem`.
The product comparison uses `WallComplement.crossingEventProduct` and
`Finset.noncommProd_map`.
-/

public section

noncomputable section

open Set Filter Topology

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V}

/-- Short transverse segments through a regular point cross exactly the walls
containing that point, simultaneously at the midpoint. No convexity or
codimension assumption on the closed supports is needed. -/
theorem eventually_exists_crossings_iff [FiniteDimensional ℝ V]
    (hclosed : ∀ j, IsClosed (W j)) {θ v : V}
    (hθ : θ ∉ singularSupport W)
    (hv : ∀ j, θ ∈ W j → v ∉ (affineSpan ℝ (W j)).direction) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement W) (_e : x ⟶ y),
        x.val = θ - a • v ∧ y.val = θ + a • v ∧
        ∀ j t, (j, t) ∈ crossings x y ↔ θ ∈ W j ∧ t = (1 / 2 : ℝ) := by
  classical
  -- Closed nonincident supports and singular support are avoided uniformly nearby.
  have hmiss := eventually_forall_lineMap_notMem_of_notMem hclosed θ
  have hreg : ∀ᶠ q : V × V in 𝓝 (θ, θ), ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap q.1 q.2 t ∉ singularSupport W :=
    (isClosed_singularSupport W hclosed).isOpen_setOf_lineMap_notMem.mem_nhds
      (by simpa using fun (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) => hθ)
  have hnear := eventually_add_smul_pair θ (-v) v (hmiss.and hreg)
  simp only [smul_neg, ← sub_eq_add_neg] at hnear
  filter_upwards [hnear, self_mem_nhdsWithin] with a ha ha0
  have ha0 : 0 < a := ha0
  -- Transversality excludes incident supports at the endpoints and gives unique crossings.
  have hnot {b : ℝ} (hb : b ≠ 0) {j : ι} (hj : θ ∈ W j) : θ + b • v ∉ W j := by
    intro hp
    have hd := (affineSpan ℝ (W j)).vsub_mem_direction
      (subset_affineSpan ℝ _ hp) (subset_affineSpan ℝ _ hj)
    have hsmul : b • v ∈ (affineSpan ℝ (W j)).direction := by simpa using hd
    exact hv j hj ((Submodule.smul_mem_iff _ hb).mp hsmul)
  let x : WallComplement W := ⟨θ - a • v, fun j hj => by
    by_cases hθj : θ ∈ W j
    · exact hnot (neg_ne_zero.mpr ha0.ne') hθj (by simpa [sub_eq_add_neg] using hj)
    · exact ha.1 j hθj 0 ⟨le_rfl, zero_le_one⟩ (by simpa using hj)⟩
  let y : WallComplement W := ⟨θ + a • v, fun j hj => by
    by_cases hθj : θ ∈ W j
    · exact hnot ha0.ne' hθj hj
    · exact ha.1 j hθj 1 ⟨zero_le_one, le_rfl⟩ (by simpa using hj)⟩
  have hd : y.val - x.val = (2 * a) • v := by dsimp [x, y]; module
  let e : x ⟶ y := ⟨{
    transverse := fun j ⟨t, ht, hj⟩ => by
      have hθj : θ ∈ W j := by
        by_contra hn
        exact ha.1 j hn t ht hj
      rw [hd]
      exact fun hm => hv j hθj ((Submodule.smul_mem_iff _ (by positivity : 2 * a ≠ 0)).mp hm)
    regular := ha.2 }⟩
  have hmid : AffineMap.lineMap x.val y.val (1 / 2 : ℝ) = θ := by
    simp only [AffineMap.lineMap_apply_module', x, y]
    module
  refine ⟨x, y, e, rfl, rfl, fun j t => ?_⟩
  have hm (hj : θ ∈ W j) : (j, (1 / 2 : ℝ)) ∈ crossings x y := by
    simp only [mem_crossings, hmid]
    exact ⟨⟨by norm_num, by norm_num⟩, hj⟩
  constructor
  · intro hj
    have hθj : θ ∈ W j := by
      by_contra hn
      exact ha.1 j hn t ((mem_crossings x y j t).mp hj).1
        ((mem_crossings x y j t).mp hj).2
    exact ⟨hθj, e.down.subsingleton_crossing j
      ((mem_crossings x y j t).mp hj) ((mem_crossings x y j _).mp (hm hθj))⟩
  · rintro ⟨hj, rfl⟩
    exact hm hj

/-- Every simultaneous crossing event of an admissible segment is the only event of a
short admissible segment through the same crossing point, in the same direction. -/
theorem exists_segmentCrossingEvents_eq_singleton [FiniteDimensional ℝ V]
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ) {x y : WallComplement W}
    (e : x ⟶ y) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    ∃ (x' y' : WallComplement W) (e' : x' ⟶ y'),
      segmentCrossingEvents ν e' = [signedCrossingEvent ν x y t] := by
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht)
  obtain ⟨a, ⟨x', y', e', hx', hy', hcross⟩, ha⟩ := ((eventually_exists_crossings_iff hclosed
    (e.down.regular t htI) fun j hj => e.down.transverse j ⟨t, htI, hj⟩).and
      self_mem_nhdsWithin).exists
  have ha : (0 : ℝ) < 2 * a := mul_pos two_pos ha
  obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
  have htimes : orderedCrossingTimes e' = [1 / 2] := by
    apply (pairwise_orderedCrossingTimes e').eq_of_mem_iff (by simp)
    intro s
    simp only [mem_orderedCrossingTimes, hcross, List.mem_singleton]
    exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨i, ((mem_crossings x y i t).mp hi).2, hs⟩⟩
  have hd : y'.val - x'.val = (2 * a) • (y.val - x.val) := by rw [hx', hy']; module
  refine ⟨x', y', e', ?_⟩
  rw [segmentCrossingEvents_def, htimes, List.map_singleton]
  congr 1
  ext ⟨j, s⟩
  simp only [mem_signedCrossingEvent, hcross, mem_crossings, hd, map_smul, smul_eq_mul,
    mul_pos_iff_of_pos_left ha, htI, true_and, and_true]

variable {G : Type*} [Group G]
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))

/-- A segment with one simultaneous crossing event computes the signed unordered
product over exactly its incident wall indices, including repeated supports. -/
theorem segmentPathProduct_eq_noncommProd_of_crossings
    {x y : WallComplement W} (e : x ⟶ y) (S : Finset ι) (t : ℝ)
    (hcross : ∀ j s, (j, s) ∈ crossings x y ↔ j ∈ S ∧ s = t)
    (comm : (S : Set ι).Pairwise (fun i j =>
      Commute (label i ^ (if 0 < ν i (y.val - x.val) then -1 else 1 : ℤ))
        (label j ^ (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ)))) :
    segmentPathProduct ν label hcomm e =
      S.noncommProd (fun j => label j ^ (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ))
        comm := by
  classical
  by_cases hS : S.Nonempty
  · have htimes : orderedCrossingTimes e = [t] := by
      apply (pairwise_orderedCrossingTimes e).eq_of_mem_iff (by simp)
      intro s
      simp only [mem_orderedCrossingTimes, hcross, List.mem_singleton]
      exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨hS.choose, hS.choose_spec, hs⟩⟩
    let emb : ι ↪ ι × ℤ := ⟨fun j => (j, if 0 < ν j (y.val - x.val) then -1 else 1),
      fun _ _ he => (Prod.mk.inj he).1⟩
    have hevent : signedCrossingEvent ν x y t = S.map emb := by
      ext ⟨j, s⟩
      simp [mem_signedCrossingEvent, hcross, emb, eq_comm]
    simp only [segmentPathProduct_def, htimes, List.reverse_singleton, List.map_singleton,
      List.prod_singleton]
    rw [crossingEventProduct_eq_noncommProd ν label hcomm e t
      (signedCrossingEvent_pairwise ν label hcomm e t)]
    exact (Finset.noncommProd_congr hevent (fun _ _ => rfl) _).trans
      (Finset.noncommProd_map S emb (fun a => label a.1 ^ a.2) _)
  · have htimes : orderedCrossingTimes e = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro s hs
      obtain ⟨j, hj⟩ := (mem_orderedCrossingTimes e s).mp hs
      exact hS ⟨j, ((hcross j s).mp hj).1⟩
    obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [segmentPathProduct_def, htimes, List.reverse_nil, List.map_nil, List.prod_nil]
    exact (Finset.noncommProd_empty _ _).symm

end Mei.Convex.WallComplement
