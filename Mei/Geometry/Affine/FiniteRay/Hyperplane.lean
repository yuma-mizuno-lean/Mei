/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Map

/-!
# Finite rays bending on one affine hyperplane

If an affine functional kills every direction increment of a finite ray, its value
along the ray is affine in time. A nonzero normal velocity therefore permits only
one encounter with each level hyperplane. When all bends lie on that hyperplane,
their support is contained in this single encounter time; if the encounter is at
or after the endpoint, the incoming ray is straight.

The argument uses `FiniteAffineRay.map_eq_straight` to retain the existing hinge
realization, including bends erased by projection.
-/

public section

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
  (β : FiniteAffineRay V P) (f : P →ᵃ[ℝ] ℝ)
  (hf : ∀ t ∈ β.bends.support, f.linear (β.bends t) = 0)

include hf

/-- Conservation of normal velocity gives the affine normal coordinate at every time. -/
theorem apply_eq_sub_mul (t : ℝ) :
    f (β t) = f β.endpoint - t * f.linear β.direction := by
  rw [← map_apply, map_eq_straight β f hf, straight_apply]
  simp [smul_eq_mul, sub_eq_add_neg, add_comm]

/-- A ray with conserved nonzero normal velocity encounters a level hyperplane
at exactly the time determined by its endpoint and final direction. -/
theorem apply_eq_iff (htrans : f.linear β.direction ≠ 0) (c t : ℝ) :
    f (β t) = c ↔ t = (f β.endpoint - c) / f.linear β.direction := by
  rw [apply_eq_sub_mul β f hf, eq_div_iff htrans]
  constructor <;> intro h <;> linarith

/-- Bends confined to one hyperplane with conserved transverse velocity have
singleton support. The encounter itself need not be an actual bend. -/
theorem support_bends_subset_singleton (htrans : f.linear β.direction ≠ 0) (c : ℝ)
    (hwall : ∀ t ∈ β.bends.support, f (β t) = c) :
    (↑β.bends.support : Set ℝ) ⊆ {(f β.endpoint - c) / f.linear β.direction} := by
  intro t ht
  exact (apply_eq_iff β f hf htrans c t).mp (hwall t ht)

/-- If the only possible hyperplane encounter is at nonnegative time, there are
no bends on the incoming half-line. This includes an encounter at the endpoint. -/
theorem eq_straight_of_nonneg_hyperplane_time (htrans : f.linear β.direction ≠ 0) (c : ℝ)
    (hwall : ∀ t ∈ β.bends.support, f (β t) = c)
    (htime : 0 ≤ (f β.endpoint - c) / f.linear β.direction) :
    β = straight β.endpoint β.direction := by
  apply FiniteAffineRay.ext
  · simp
  · simp
  · apply Finsupp.ext
    intro t
    by_cases ht : t ∈ β.bends.support
    · have he := support_bends_subset_singleton β f hf htrans c hwall ht
      exact False.elim ((not_lt_of_ge (he ▸ htime)) (β.bend_neg t ht))
    · simpa only [bends_straight, Finsupp.zero_apply] using
        Finsupp.notMem_support_iff.mp ht

/-- A ray parallel to the hyperplane and ending off it cannot bend on it.
This also allows zero final and incoming velocity. -/
theorem eq_straight_of_parallel (c : ℝ)
    (hwall : ∀ t ∈ β.bends.support, f (β t) = c)
    (hoff : f β.endpoint ≠ c) (hparallel : f.linear β.direction = 0) :
    β = straight β.endpoint β.direction := by
  have hnormal (t : ℝ) : f (β t) = f β.endpoint := by
    simp only [apply_eq_sub_mul β f hf, hparallel, mul_zero, sub_zero]
  have hb : β.bends = 0 := by
    ext t
    by_cases ht : t ∈ β.bends.support
    · exact False.elim (hoff ((hnormal t).symm.trans (hwall t ht)))
    · exact Finsupp.notMem_support_iff.mp ht
  apply FiniteAffineRay.ext <;> simp [hb]

end Mei.FiniteAffineRay
