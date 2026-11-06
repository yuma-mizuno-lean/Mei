/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Degeneration
public import Mei.Geometry.Convex.Polyhedron.Tangent

/-!
# Rescaling backward itineraries at a common center

When the selected hyperplanes pass through a common point, simultaneous scaling
of space and time identifies their backward reconstruction with the reconstruction
for the corresponding hyperplanes through zero. Velocities stay fixed. The
identity holds for the entire hinge extension, including collapsed encounters
and the incoming half-line, without a time-order or transversality hypothesis.

For polyhedral selected supports through the center, sufficiently small positive
scales identify the selected-incidence endpoint domain with the domain for their
positive tangent cones. This comparison is uniform on compact endpoint sets.
It supplies the incidence and path comparisons used when studying local broken-line
resolutions by rescaling their closed endpoint charts. Avoidance of other walls,
singular sets and incoming-source conditions are separate constraints.

We use the existing backward reconstruction and the local tangent-cone description
of a convex polyhedron. The interpretation of closed broken-line charts follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (u : Fin n → V) (z Q : V) (r : ℝ)

/-- With all hyperplanes centered at `z`, reconstruction commutes with spatial
scaling. The identity includes zero and negative scales and tangent steps. -/
@[simp↓]
theorem backwardPoint_add_smul (j : Fin (n + 1)) :
    backwardPoint f (fun i => f i z) u j (z + r • Q) =
      z + r • backwardPoint f 0 u j Q := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have ht : backwardTime f (fun i => f i z) u j (z + r • Q) =
        r * backwardTime f 0 u j Q := by
      rw [backwardTime_apply, ih, backwardTime_apply]
      simp only [map_add, map_smul, smul_eq_mul, Pi.zero_apply]
      ring
    rw [backwardPoint_succ_apply, backwardPoint_succ_apply, ih, ht]
    module

/-- Elapsed times scale by the same factor as space; velocities are unchanged. -/
@[simp↓]
theorem backwardTime_add_smul (j : Fin n) :
    backwardTime f (fun i => f i z) u j (z + r • Q) =
      r * backwardTime f 0 u j Q := by
  rw [backwardTime_apply, backwardPoint_add_smul, backwardTime_apply]
  simp only [map_add, map_smul, smul_eq_mul, Pi.zero_apply]
  ring

/-- Every cumulative encounter parameter scales with space, even when some
elapsed times vanish or have the wrong sign for an actual realization. -/
@[simp↓]
theorem backwardParameter_add_smul (j : Fin (n + 1)) :
    backwardParameter f (fun i => f i z) u j (z + r • Q) =
      r * backwardParameter f 0 u j Q := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [backwardParameter_succ, backwardParameter_succ, ih, backwardTime_add_smul]
    ring

variable (v : Fin (n + 1) → V)

/-- Shrinking space and time together preserves the full extended path,
including the incoming tail and collapsed encounters. Nonnegative scaling is
needed because the hinge formula distinguishes the two time directions. -/
@[simp↓]
theorem backwardPath_add_smul {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    backwardPath f (fun i => f i z) v (z + r • Q) (r * t) =
      z + r • backwardPath f 0 v Q t := by
  have hmax (a : ℝ) : max (r * a) 0 = r * max a 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg a 0 hr).symm
  simp only [backwardPath_apply, backwardParameter_add_smul, ← mul_sub, hmax, mul_smul]
  rw [← Finset.smul_sum]
  module

variable (P : Fin n → Set V)

/-- Every reconstructed encounter has the same support incidence as its tangent
counterpart, uniformly on a compact endpoint set at small positive scales. -/
theorem eventually_forall_backwardPoint_mem_add_smul_iff
    (hP : ∀ j, TauCeti.IsConvexPolyhedron (P j)) (hz : ∀ j, z ∈ P j)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K, ∀ j,
      backwardPoint f (fun i => f i z) u j.succ (z + r • Q) ∈ P j ↔
        backwardPoint f 0 u j.succ Q ∈ posTangentConeAt (P j) z := by
  have hlocal (j : Fin n) :
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
        z + r • backwardPoint f 0 u j.succ Q ∈ P j ↔
          backwardPoint f 0 u j.succ Q ∈ posTangentConeAt (P j) z := by
    have hb := (hK.image (backwardPoint f 0 u j.succ).continuous).isBounded
    have he := eventually_singleton_add_smul_subset (𝕜 := ℝ) hb
      ((hP j).eventually_mem_iff_sub_mem_posTangentConeAt (hz j))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrpos
    intro Q hQ
    have hc := hr (Set.add_mem_add (Set.mem_singleton z)
      (Set.smul_mem_smul_set (mem_image_of_mem _ hQ)))
    simp only [mem_ofPred_eq, add_sub_cancel_left] at hc
    refine hc.trans ⟨?_, fun h => Mei.smul_mem_posTangentConeAt h hrpos.le⟩
    intro h
    simpa only [smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul] using
      Mei.smul_mem_posTangentConeAt h (inv_pos.mpr hrpos).le
  filter_upwards [eventually_all.mpr hlocal] with r hr
  intro Q hQ j
  rw [backwardPoint_add_smul]
  exact hr j Q hQ

/-- On a compact set of endpoint displacements, all selected support incidences
and strict elapsed-time inequalities agree with those of the tangent supports
for every sufficiently small positive scale. Repeated supports are allowed. -/
theorem eventually_forall_mem_backwardDomain_add_smul_iff
    (hP : ∀ j, TauCeti.IsConvexPolyhedron (P j)) (hz : ∀ j, z ∈ P j)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
      z + r • Q ∈ backwardDomain f (fun i => f i z) u P ↔
        Q ∈ backwardDomain f 0 u (fun j => posTangentConeAt (P j) z) := by
  filter_upwards [eventually_forall_backwardPoint_mem_add_smul_iff f u z P hP hz hK,
    self_mem_nhdsWithin] with r hr hrpos
  intro Q hQ
  simp only [mem_backwardDomain, backwardTime_add_smul, mul_pos_iff_of_pos_left hrpos]
  exact forall_congr' fun j => and_congr_right fun _ => hr Q hQ j

/-- The same local incidence comparison retains zero elapsed times, as required
for closed charts with terminal or collapsed encounters. -/
theorem eventually_forall_mem_weakBackwardDomain_add_smul_iff
    (hP : ∀ j, TauCeti.IsConvexPolyhedron (P j)) (hz : ∀ j, z ∈ P j)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
      z + r • Q ∈ weakBackwardDomain f (fun i => f i z) u P ↔
        Q ∈ weakBackwardDomain f 0 u (fun j => posTangentConeAt (P j) z) := by
  filter_upwards [eventually_forall_backwardPoint_mem_add_smul_iff f u z P hP hz hK,
    self_mem_nhdsWithin] with r hr hrpos
  intro Q hQ
  simp only [mem_weakBackwardDomain, backwardTime_add_smul,
    mul_nonneg_iff_of_pos_left hrpos]
  exact forall_congr' fun j => and_congr_right fun _ => hr Q hQ j

end Mei.Convex
