/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
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
open scalar half-lines.
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

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V}

/-- Near a point, matching strict normal sides at its incident supports suffice
for the entire connecting segment to miss all supports. -/
theorem eventually_forall_lineMap_notMem_of_mul_pos
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ j, (affineSpan ℝ (W j)).direction ≤ LinearMap.ker (ν j)) (θ : V) :
    ∀ᶠ z : V × V in 𝓝 (θ, θ),
      (∀ j, θ ∈ W j → 0 < ν j (z.1 - θ) * ν j (z.2 - θ)) →
      ∀ j t, t ∈ Icc (0 : ℝ) 1 → AffineMap.lineMap z.1 z.2 t ∉ W j := by
  have hmiss : ∀ᶠ z : V × V in 𝓝 (θ, θ), ∀ j, θ ∉ W j →
      ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap z.1 z.2 t ∉ W j := by
    apply eventually_all.mpr
    intro j
    apply eventually_imp_distrib_left.mpr
    intro hj
    exact (hclosed j).isOpen_setOf_lineMap_notMem.mem_nhds
      (by simpa using fun (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) => hj)
  filter_upwards [hmiss] with z hz hsign j t ht
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
