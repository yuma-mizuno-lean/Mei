/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Factor

/-!
# Logarithms of completed labels as sums over supported rays

At every order, the logarithm of a completed label is the sum of the logarithms of its ray
factors over any finite set of supported rays containing the rays that meet the cutoff
(`PositiveDegrees.log_projection_eq_sum_log_projection_rayFactor`). Unlike the product formula
`PositiveDegrees.projection_eq_noncommProd_rayFactor`, no commutation of the logarithmic
coefficients is needed: logarithms of ray factors are sums of disjoint sets of homogeneous
coefficients. The proof combines `PositiveDegrees.log_projection_rayFactor` with
`PositiveDegrees.log_projection_eq_mkQ_sum`, using that every nonzero allowed degree lies on
exactly one supported ray.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

namespace TauCeti.PositiveDegrees

open Mei

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- At order `k`, the logarithm of a completed label is the sum of the logarithms of its ray
factors over any finite set of supported rays containing those that meet the cutoff. -/
theorem log_projection_eq_sum_log_projection_rayFactor [Module.Free ℤ N]
    (g : d.completedBCHGroup ℒ) (k : ℕ) (s : Finset (SupportedRay d))
    (hs : d.raysAtOrder k ⊆ s) :
    BCHGroup.log (L := d.lieTruncation ℒ k) (TauCeti.CompletedGroup.projection k g) =
      ∑ w ∈ s, BCHGroup.log (L := d.lieTruncation ℒ k)
        (TauCeti.CompletedGroup.projection k (d.rayFactor ℒ g w)) := by
  classical
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  simp only [log_projection_eq_mkQ_sum, ← map_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hP, hk⟩ := d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hn)
  have hz (x : ℒ 0) : (x : L) = 0 := by
    simpa only [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) 0 (Or.inr rfl), Submodule.mem_bot]
      using x.property
  by_cases h0 : n = 0
  · subst h0
    simp only [hz, Finset.sum_const_zero]
  obtain ⟨w, hw⟩ := d.exists_supportedRay hP h0
  rw [Finset.sum_eq_single_of_mem w (hs (d.mem_raysAtOrder.mpr ⟨n, hw, hk⟩)),
    d.logComponent_rayFactor_of_mem ℒ g hw]
  intro v _ hvw
  rw [d.logComponent_rayFactor_of_notMem ℒ g
    fun hv => hvw (SupportedRay.eq_of_mem_rayDegrees hv hw), ZeroMemClass.coe_zero]

end TauCeti.PositiveDegrees
