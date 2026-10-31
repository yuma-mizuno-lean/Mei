/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Extend
public import Mei.Geometry.Affine.FiniteRay.Truncate

/-!
# Inverse laws for cutting and attaching finite affine rays

Cutting an attached ray at the original endpoint recovers the entire incoming
ray. Conversely, a cut before the final possible bend can be reattached to
recover the original ray. The encounter need not be an actual bend: equal
incoming and outgoing directions, and stationary segments, are allowed.

These are the geometric inverse laws for the cut/glue correspondence in
last-encounter recursions for broken lines. The operations and their parameter
conventions are those of `FiniteAffineRay.extend` and `FiniteAffineRay.truncate`;
the reconstruction uses `FiniteAffineRay.eval_vsub_eval` and
`FiniteAffineRay.directionAt_sub_eq_bends`. For the broken-line recursion see
Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Cutting an extension at the original endpoint recovers the incoming ray,
including its bend data. The cut may coincide with the newly attached encounter. -/
@[simp↓]
theorem truncate_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) :
    (β.extend s t w hs ht).truncate (-(s + t)) = β := by
  apply FiniteAffineRay.ext
  · simpa using β.extend_apply_sub s t w hs ht (u := 0) le_rfl
  · rw [direction_truncate, directionAt_extend_of_le _ _ _ _ hs ht (by linarith)]
    simp
  · ext u
    rw [bends_truncate_apply]
    by_cases hu : u < 0
    · rw [ite_eq_left hu, bends_extend_apply]
      have hne : u + -(s + t) ≠ -t := by linarith
      rw [ite_eq_right hne, add_zero]
      congr 1
      ring
    · rw [ite_eq_right hu]
      exact (Finsupp.notMem_support_iff.mp (fun hb => hu (β.bend_neg u hb))).symm

/-- Attachment with fixed durations and outgoing direction is injective on
incoming rays. This retains the full incoming path, rather than just its tail. -/
theorem extend_injective (s t : ℝ) (w : V) (hs : 0 ≤ s) (ht : 0 < t) :
    Function.Injective (fun β : FiniteAffineRay V P => β.extend s t w hs ht) := by
  intro β γ h
  have := congrArg (fun δ : FiniteAffineRay V P => δ.truncate (-(s + t))) h
  simpa only [truncate_extend] using this

/-- A ray can be reconstructed from a cut before its last possible bend. Every
other bend must precede the cut; no nonzero increment at `b` is required. -/
theorem extend_truncate (β : FiniteAffineRay V P) {u b : ℝ}
    (hub : u < b) (hb : b < 0)
    (hbends : ∀ a ∈ β.bends.support, a < u ∨ a = b) :
    (β.truncate u).extend (b - u) (-b) β.direction
      (by linarith) (by linarith) = β := by
  classical
  -- The cut lies in a straight piece. Its direction differs from the final
  -- direction by precisely the increment at the selected encounter.
  have hu₀ : β.bends u = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hu
    rcases hbends u hu with h | h
    · exact h.false
    · exact hub.ne h
  have hgap : ∀ a ∈ β.bends.support, a ≤ u ∨ b ≤ a := by
    intro a ha
    rcases hbends a ha with h | rfl
    · exact Or.inl h.le
    · exact Or.inr le_rfl
  have hdir : β.directionAt u = β.directionAt b := by
    have he := β.directionAt_sub_eq_bends hub hgap
    rwa [hu₀, sub_eq_zero] at he
  have hlast : ∀ a ∈ β.bends.support, a ≤ b := by
    intro a ha
    rcases hbends a ha with h | rfl
    · exact h.le.trans hub.le
    · exact le_rfl
  have hinc : β.directionAt u - β.direction = β.bends b := by
    rw [hdir, ← β.directionAt_of_nonneg (u := 0) le_rfl]
    exact β.directionAt_sub_eq_bends hb (fun a ha => Or.inl (hlast a ha))
  apply FiniteAffineRay.ext
  -- The two straight displacements recover the original endpoint.
  · rw [endpoint_extend, endpoint_truncate, direction_truncate]
    have h₁ := β.eval_vsub_eval hub.le hgap
    have h₂ := β.eval_vsub_eval hb.le (fun a ha => Or.inl (hlast a ha))
    simp only [eval_zero, sub_zero, directionAt_of_nonneg β le_rfl] at h₂
    calc
      (- (b - u) • β.directionAt u - -b • β.direction) +ᵥ β u =
          (b • β.direction) +ᵥ ((u - b) • β.directionAt b +ᵥ β u) := by
            rw [vadd_vadd, hdir]
            congr 1
            module
      _ = (b • β.direction) +ᵥ β b := by rw [← h₁, vsub_vadd]
      _ = β.endpoint := by rw [← h₂, vsub_vadd]
  · exact direction_extend ..
  -- Earlier increments survive the cut; the selected increment is restored.
  · ext a
    rw [bends_extend_apply, direction_truncate, hinc, bends_truncate_apply]
    have htime : a + (b - u + -b) = a - u := by ring
    rw [htime]
    simp only [neg_neg]
    by_cases hau : a < u
    · have hne : a ≠ b := (hau.trans hub).ne
      simp [sub_neg.mpr hau, hne]
    · rw [ite_eq_right (by linarith : ¬a - u < 0)]
      by_cases hab : a = b
      · simp [hab]
      · have ha₀ : β.bends a = 0 := by
          apply Finsupp.notMem_support_iff.mp
          intro ha
          exact (hbends a ha).elim hau hab
        simp [hab, ha₀]

end Mei.FiniteAffineRay
