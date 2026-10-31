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
