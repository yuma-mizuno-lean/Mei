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
their generic perturbations, using
`Mei.eventually_forall_lineMap_notMem_of_mul_pos` for segment avoidance.
-/

public section

open Set Filter Topology

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V}

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
