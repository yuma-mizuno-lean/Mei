/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Extend
public import Mei.Geometry.Affine.FiniteRay.Truncate

/-!
# Cutting and reattaching finite affine rays

Cutting an extended ray at its old endpoint recovers the original ray. Conversely,
cutting before or at its final encounter and reattaching the two discarded
straight segments recovers the entire ray, including its bend increments.
The final encounter need not be an actual bend: equal spatial directions are allowed.

These are the geometric inverse laws used in cutting broken lines at their last
change of decoration. They combine `FiniteAffineRay.truncate` and
`FiniteAffineRay.extend`, using the hinge presentation in `FiniteAffineRay.Basic`.
See Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Cutting an extension at its original endpoint recovers the original ray,
even when the new encounter has no direction change or the continuation time is zero. -/
@[simp↓]
theorem truncate_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) :
    (β.extend s t w hs ht).truncate (-(s + t)) = β := by
  apply FiniteAffineRay.ext
  · simpa only [endpoint_truncate, zero_sub, eval_zero] using
      β.extend_apply_sub s t w hs ht (u := 0) le_rfl
  · rw [direction_truncate,
      directionAt_extend_of_le _ _ _ _ hs ht (by linarith), neg_add_cancel,
      directionAt_of_nonneg _ le_rfl]
  · ext u
    rw [bends_truncate_apply]
    by_cases hu : u < 0
    · rw [ite_eq_left hu, bends_extend_apply]
      simp only [neg_add_cancel_right]
      rw [ite_eq_right (by intro h; linarith), add_zero]
    · rw [ite_eq_right hu]
      exact (Finsupp.notMem_support_iff.mp (fun h => hu (β.bend_neg u h))).symm

/-- Reattach the final encounter after a cut in the preceding segment or at the encounter.
The two lengths and the final direction are recovered from the original ray.
The result is equality of finite rays, rather than just equality on the retained tail. -/
@[simp]
theorem extend_truncate (β : FiniteAffineRay V P) {a b : ℝ}
    (hab : a ≤ b) (hb₀ : b < 0)
    (hb : ∀ u ∈ β.bends.support, u < a ∨ u = b) :
    (β.truncate a).extend (b - a) (-b) β.direction
      (sub_nonneg.mpr hab) (neg_pos.mpr hb₀) = β := by
  classical
  have hdir : β.directionAt a = β.directionAt b := by
    rcases hab.eq_or_lt with rfl | hlt
    · rfl
    · have hcut : β.bends a = 0 := Finsupp.notMem_support_iff.mp (by
        intro ha
        exact (hb a ha).elim (lt_irrefl a) (fun h => hlt.ne h))
      have h := β.directionAt_sub_eq_bends hlt (fun u hu =>
        (hb u hu).imp (fun h => h.le) (fun h => h.ge))
      rwa [hcut, sub_eq_zero] at h
  have hstep₁ := β.eval_vsub_eval hab (fun u hu =>
    (hb u hu).imp (fun h => h.le) (fun h => h.ge))
  have hstep₂ := β.eval_vsub_eval hb₀.le (fun u hu =>
    (hb u hu).elim (fun h => Or.inl (h.le.trans hab)) (fun h => Or.inl h.le))
  rw [eval_zero, directionAt_of_nonneg _ le_rfl] at hstep₂
  have hpoint : β.endpoint = ((a - b) • β.directionAt a +
      b • β.direction) +ᵥ β a := by
    rw [sub_zero] at hstep₂
    rw [hdir, ← hstep₁, ← hstep₂, add_comm, vsub_add_vsub_cancel, vsub_vadd]
  have hincrement : β.directionAt a - β.direction = β.bends b := by
    rw [hdir, ← β.directionAt_of_nonneg (u := 0) le_rfl]
    exact β.directionAt_sub_eq_bends hb₀ (fun u hu =>
      (hb u hu).elim (fun h => Or.inl (h.le.trans hab)) (fun h => Or.inl h.le))
  apply FiniteAffineRay.ext
  · rw [endpoint_extend, endpoint_truncate, direction_truncate, hpoint]
    congr 1
    module
  · exact direction_extend ..
  · ext u
    rw [bends_extend_apply, bends_truncate_apply, direction_truncate, hincrement]
    have hshift : u + (b - a + -b) + a = u := by ring
    rw [hshift]
    by_cases hua : u < a
    · rw [ite_eq_left (by linarith), ite_eq_right (by intro h; linarith), add_zero]
    · rw [ite_eq_right (by linarith), zero_add]
      by_cases hub : u = b
      · simp [hub]
      · rw [ite_eq_right (by simpa using hub)]
        exact (Finsupp.notMem_support_iff.mp
          (fun hu => (hb u hu).elim hua hub)).symm

end Mei.FiniteAffineRay
