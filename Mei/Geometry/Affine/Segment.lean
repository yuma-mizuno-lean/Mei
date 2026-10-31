/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Stability of segments avoiding a closed set

Pairs of endpoints whose closed segment avoids a closed obstacle form an open
set. This supplies the compact-parameter part of stability for transverse
polygonal paths. The proof uses Mathlib's closedness of projection along a
compact space, applied to the unit interval of segment parameters.

For a finite family of closed supports, endpoints sufficiently near one point
also have an avoiding segment whenever their normal evaluations have matching
nonzero signs at every incident support. Nonincident supports are excluded by
`IsClosed.isOpen_setOf_lineMap_notMem`, and incident ones by convexity of the
open scalar half-lines. A transverse incoming segment may instead end on an
incident wall while avoiding every singular set through its regular endpoint.
Extending beyond the last marked encounter keeps closed obstacles off unmarked
points and singular sets off the whole segment, using only the last encounter's
transverse normal. Reversing the extended segment gives decreasing encounter
times measured from its new endpoint.
-/

public section

open Set

namespace IsClosed

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]

/-- Avoiding a closed obstacle along an entire closed segment is an open
condition on its two endpoints. -/
theorem isOpen_setOf_lineMap_notMem {S : Set P} (hS : IsClosed S) :
    IsOpen {p : P × P | ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∉ S} := by
  have hc : Continuous (fun q : (P × P) × Icc (0 : ℝ) 1 =>
      AffineMap.lineMap q.1.1 q.1.2 (q.2 : ℝ)) :=
    continuous_fst.fst.lineMap continuous_fst.snd
      (continuous_subtype_val.comp continuous_snd)
  have hclosed := isClosedMap_fst_of_compactSpace _ (hS.preimage hc)
  convert hclosed.isOpen_compl using 1
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, mem_preimage, Prod.exists,
    not_exists, not_and, Subtype.forall]
  aesop

end IsClosed

namespace Mei

open Filter Topology

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [Finite ι] {W : ι → Set V}

/-- Near a point, segments avoid every member of a finite family of closed
sets that does not contain that point. -/
theorem eventually_forall_lineMap_notMem_of_notMem
    (hclosed : ∀ j, IsClosed (W j)) (θ : V) :
    ∀ᶠ z : V × V in 𝓝 (θ, θ), ∀ j, θ ∉ W j →
      ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap z.1 z.2 t ∉ W j := by
  apply eventually_all.mpr
  intro j
  apply eventually_imp_distrib_left.mpr
  intro hj
  exact (hclosed j).isOpen_setOf_lineMap_notMem.mem_nhds
    (by simpa using fun (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) => hj)

/-- An eventual property of endpoint pairs near a diagonal point holds along
two affine germs at every sufficiently small positive parameter. -/
theorem eventually_add_smul_pair (θ v w : V) {p : V × V → Prop}
    (hp : ∀ᶠ z in 𝓝 (θ, θ), p z) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, p (θ + ε • v, θ + ε • w) := by
  have hc : Continuous (fun ε : ℝ => (θ + ε • v, θ + ε • w)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => (θ + ε • v, θ + ε • w))
      (𝓝 0) (𝓝 (θ, θ)) := by
    simpa using hc.tendsto 0
  exact (ht.eventually hp).filter_mono nhdsWithin_le_nhds

/-- For sufficiently small incoming displacements, the segment with parameter
`0 < u < η` avoids closed walls and singular sets. Singular sets are also avoided
at `u = η` when the transverse endpoint `x` is regular. Incident walls lie in
the crossing hyperplane. -/
theorem eventually_incomingSegment_notMem {κ : Type*} [Finite κ]
    {S : κ → Set V} (x v : V) (m : V →ₗ[ℝ] ℝ) (b : ℝ)
    (htrans : m v ≠ 0) (hheight : m x = b)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, x ∈ W j → ∀ y ∈ W j, m y = b)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, x ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∀ j u, 0 < u → u < η → x + η • v - u • v ∉ W j) ∧
      (∀ j u, 0 < u → u ≤ η → x + η • v - u • v ∉ S j) := by
  have hnear := eventually_add_smul_pair x v 0
    ((eventually_forall_lineMap_notMem_of_notMem hclosedW x).and
      (eventually_forall_lineMap_notMem_of_notMem hclosedS x))
  filter_upwards [hnear, self_mem_nhdsWithin] with η hnear hη
  have hη : 0 < η := hη
  have hline (u : ℝ) : AffineMap.lineMap (x + η • v) (x + η • (0 : V)) (u / η) =
      x + η • v - u • v := by
    simp only [AffineMap.lineMap_apply_module', smul_zero, add_zero, smul_sub,
      smul_add, smul_smul, div_mul_cancel₀ u hη.ne']
    module
  constructor
  · intro j u hu huη hy
    by_cases hj : x ∈ W j
    · have he := hplane j hj _ hy
      have he' : m (x + η • v - u • v) = b + (η - u) * m v := by
        rw [map_sub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hheight]
        ring
      rw [he'] at he
      exact (mul_ne_zero (sub_pos.mpr huη).ne' htrans) (by linarith)
    · apply hnear.1 j hj (u / η) ⟨(div_pos hu hη).le, (div_lt_one hη).mpr huη |>.le⟩
      rw [hline]
      exact hy
  · intro j u hu huη
    have hh := hnear.2 j (hregular j) (u / η)
      ⟨(div_pos hu hη).le, (div_le_one hη).mpr huη⟩
    rw [hline] at hh
    exact hh

/-- Extend a segment a short distance beyond its last marked point. Closed
obstacles still miss the extended segment away from the marked wall encounters;
singular sets miss the whole segment, including every encounter. Only the
normal of the last encounter is needed for the new short piece. -/
theorem eventually_extendSegment_notMem {κ : Type*} [Finite κ]
    {S : κ → Set V} {n : ℕ} (Q v : V) (s : Fin (n + 1) → ℝ)
    (hs : 0 ≤ s (Fin.last n)) (m : V →ₗ[ℝ] ℝ) (b : ℝ)
    (htrans : m v ≠ 0) (hheight : m (Q + s (Fin.last n) • v) = b)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + s (Fin.last n) • v ∈ W j → ∀ y ∈ W j, m y = b)
    (hclosedS : ∀ j, IsClosed (S j))
    (hW : ∀ j t, 0 ≤ t → t < s (Fin.last n) →
      (∀ i, t ≠ s i) → Q + t • v ∉ W j)
    (hS : ∀ j t, 0 ≤ t → t ≤ s (Fin.last n) → Q + t • v ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∀ j u, 0 < u → u ≤ s (Fin.last n) + η →
        (∀ i, u ≠ s (Fin.last n) + η - s i) →
        Q + (s (Fin.last n) + η) • v - u • v ∉ W j) ∧
      (∀ j u, 0 < u → u ≤ s (Fin.last n) + η →
        Q + (s (Fin.last n) + η) • v - u • v ∉ S j) := by
  let t := s (Fin.last n)
  let x := Q + t • v
  have hnear := eventually_incomingSegment_notMem x v m b htrans hheight
    hclosedW hplane hclosedS (fun j => hS j t hs le_rfl)
  filter_upwards [hnear] with η hnear
  have hpoint (u : ℝ) : Q + (t + η) • v - u • v = Q + (t + η - u) • v := by module
  have hshort (u : ℝ) : x + η • v - u • v = Q + (t + η - u) • v := by
    dsimp only [x]
    module
  constructor
  · intro j u hu huL huτ
    rw [hpoint]
    by_cases huη : η < u
    · apply hW j (t + η - u) (by linarith) (by linarith)
      intro i he
      exact huτ i (by linarith)
    · have hule : u ≤ η := le_of_not_gt huη
      have hstrict : u < η := lt_of_le_of_ne hule (by
        simpa only [t, add_sub_cancel_left] using huτ (Fin.last n))
      simpa only [hshort] using hnear.1 j u hu hstrict
  · intro j u hu huL
    rw [hpoint]
    by_cases huη : η ≤ u
    · exact hS j (t + η - u) (by linarith) (by linarith)
    · simpa only [hshort] using hnear.2 j u hu (le_of_not_ge huη)

/-- Extend a marked straight segment and measure its encounter times backward
from the new endpoint. The reversed times are positive, strictly decreasing and
less than the segment length; the marked points remain on their prescribed
supports, while walls and singular sets are avoided between encounters. -/
theorem eventually_extendSegment {κ : Type*} [Finite κ]
    {S : κ → Set V} {n : ℕ} (Q v : V) (s : Fin (n + 1) → ℝ)
    (hs : StrictMono s) (hpos : ∀ i, 0 < s i)
    (g : Fin (n + 1) → V →ₗ[ℝ] ℝ) (b : Fin (n + 1) → ℝ)
    (H : Fin (n + 1) → Set V)
    (htrans : g (Fin.last n) v ≠ 0)
    (hheight : ∀ i, g i (Q + s i • v) = b i)
    (hinc : ∀ i, Q + s i • v ∈ H i)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + s (Fin.last n) • v ∈ W j →
      ∀ y ∈ W j, g (Fin.last n) y = b (Fin.last n))
    (hclosedS : ∀ j, IsClosed (S j))
    (hW : ∀ j t, 0 ≤ t → t < s (Fin.last n) →
      (∀ i, t ≠ s i) → Q + t • v ∉ W j)
    (hS : ∀ j t, 0 ≤ t → t ≤ s (Fin.last n) → Q + t • v ∉ S j) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      let L := s (Fin.last n) + η
      let Y := Q + L • v
      let τ := fun i => L - s i
      Y - L • v = Q ∧ 0 ≤ L ∧ StrictAnti τ ∧
        (∀ i, 0 < τ i) ∧ (∀ i, τ i < L) ∧
        (∀ i, g i (Y - τ i • v) = b i) ∧
        (∀ i, Y - τ i • v ∈ H i) ∧
        (∀ j u, 0 < u → u ≤ L → (∀ i, u ≠ τ i) → Y - u • v ∉ W j) ∧
        (∀ j u, 0 < u → u ≤ L → Y - u • v ∉ S j) := by
  have hnear := eventually_extendSegment_notMem Q v s (hpos _).le
    (g (Fin.last n)) (b (Fin.last n)) htrans (hheight _)
    hclosedW hplane hclosedS hW hS
  filter_upwards [hnear, self_mem_nhdsWithin] with η hnear hη
  have hη : 0 < η := hη
  have hpoint (i : Fin (n + 1)) :
      Q + (s (Fin.last n) + η) • v - (s (Fin.last n) + η - s i) • v =
        Q + s i • v := by module
  exact ⟨by simp, by linarith [hpos (Fin.last n)],
    fun i j hij => by dsimp only; linarith [hs hij],
    fun i => by dsimp only; linarith [hs.monotone (Fin.le_last i)],
    fun i => by dsimp only; linarith [hpos i],
    fun i => by simpa only [hpoint] using hheight i,
    fun i => by simpa only [hpoint] using hinc i, hnear⟩

/-- Near a point, matching strict normal sides at its incident supports suffice
for the entire connecting segment to miss all supports. -/
theorem eventually_forall_lineMap_notMem_of_mul_pos
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ j, (affineSpan ℝ (W j)).direction ≤ LinearMap.ker (ν j)) (θ : V) :
    ∀ᶠ z : V × V in 𝓝 (θ, θ),
      (∀ j, θ ∈ W j → 0 < ν j (z.1 - θ) * ν j (z.2 - θ)) →
      ∀ j t, t ∈ Icc (0 : ℝ) 1 → AffineMap.lineMap z.1 z.2 t ∉ W j := by
  filter_upwards [eventually_forall_lineMap_notMem_of_notMem hclosed θ] with z hz hsign j t ht
  by_cases hj : θ ∈ W j
  · intro hmem
    have hzero : ν j (AffineMap.lineMap z.1 z.2 t - θ) = 0 :=
      hν j ((affineSpan ℝ (W j)).vsub_mem_direction
        (subset_affineSpan ℝ _ hmem) (subset_affineSpan ℝ _ hj))
    have he : ν j (AffineMap.lineMap z.1 z.2 t - θ) =
        AffineMap.lineMap (ν j (z.1 - θ)) (ν j (z.2 - θ)) t := by
      simp only [AffineMap.lineMap_apply_module', map_sub, map_add, map_smul,
        smul_eq_mul]
      ring
    rcases mul_pos_iff.mp (hsign j hj) with hpos | hneg
    · have hp := (convex_Ioi (0 : ℝ)).lineMap_mem hpos.1 hpos.2 ht
      rw [← he, hzero] at hp
      exact (lt_irrefl 0) hp
    · have hn := (convex_Iio (0 : ℝ)).lineMap_mem hneg.1 hneg.2 ht
      rw [← he, hzero] at hn
      exact (lt_irrefl 0) hn
  · exact hz j hj t ht

end Mei
