/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mei.Geometry.Affine.Segment

/-!
# Comparing affine germs on the same side of walls

For a finite family of closed supports, two sufficiently short affine germs from
one point can be joined without meeting any support if their normal evaluations
have the same nonzero signs at the incident supports. Nonincident supports are
excluded by closedness. No regularity of the base point, convexity of the supports,
or finite-dimensionality is needed.

This supplies wall-free connecting segments between straight incoming germs and
their generic perturbations. We use `IsClosed.isOpen_setOf_lineMap_notMem` for
nonincident supports and convexity of the open scalar half-lines for incident ones.
-/

public section

open Set Filter Topology

namespace Mei.Convex.WallComplement

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

/-- Affine germs with matching nonzero incident normal signs admit wall-free
connecting segments at every sufficiently small positive parameter. -/
theorem eventually_exists_crossings_eq_empty_of_mul_pos
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ j, (affineSpan ℝ (W j)).direction ≤ LinearMap.ker (ν j))
    (θ v w : V) (hsign : ∀ j, θ ∈ W j → 0 < ν j v * ν j w) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∃ x y : WallComplement W, x.val = θ + ε • v ∧ y.val = θ + ε • w ∧
        crossings x y = ∅ := by
  have hc : Continuous (fun ε : ℝ => (θ + ε • v, θ + ε • w)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => (θ + ε • v, θ + ε • w))
      (𝓝 0) (𝓝 (θ, θ)) := by
    simpa using hc.tendsto 0
  filter_upwards [(ht.eventually
    (eventually_forall_lineMap_notMem_of_mul_pos hclosed ν hν θ)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hεpos
  have hεpos : 0 < ε := hεpos
  have hnot := hε (fun j hj => by
    simpa only [add_sub_cancel_left, map_smul, smul_eq_mul,
      mul_mul_mul_comm ε _ ε _] using mul_pos (mul_self_pos.mpr hεpos.ne') (hsign j hj))
  let x : WallComplement W := ⟨θ + ε • v, fun j hm =>
    hnot j 0 ⟨le_rfl, zero_le_one⟩ (by simpa using hm)⟩
  let y : WallComplement W := ⟨θ + ε • w, fun j hm =>
    hnot j 1 ⟨zero_le_one, le_rfl⟩ (by simpa using hm)⟩
  refine ⟨x, y, rfl, rfl, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro ⟨j, t⟩ hm
  rw [mem_crossings] at hm
  exact hnot j t hm.1 hm.2

end Mei.Convex.WallComplement
