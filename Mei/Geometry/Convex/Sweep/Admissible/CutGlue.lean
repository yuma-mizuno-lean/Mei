/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Affine.FiniteRay.CutGlue

/-!
# Reconstructing admissible rays from incoming cuts

Suppose the directions after a selected encounter all agree with the final
direction. Cutting just before that encounter and attaching the two straight
pieces recovers the entire finite affine ray. Later recorded encounters are
allowed: their equal adjacent directions force their bend increments to vanish.
The selected encounter can itself have zero bend.

This supplies the geometric reconstruction at the last change of decoration
of a broken line, including changes with zero spatial projection. The theorem
combines `AdmissibleRayRealization.bends_parameter` with the inverse law
`FiniteAffineRay.extend_truncate`; it concerns the path, while the complete
encounter inventory remains recorded in the original admissible realization.
For the last-change recursion see Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Reattach an incoming cut before an encounter followed only by unchanged
directions. Recover the full path, including every earlier bend and the entire
incoming half-line. No nonzero bend at the chosen encounter is required. -/
theorem ray_extend_truncate (r : AdmissibleRayRealization f c v P W S C Q)
    (j : Fin n) {u : ℝ} (hbefore : u < r.parameter j.succ)
    (hafter : ∀ k : Fin n, j < k → r.parameter k.succ < u)
    (hv : ∀ i ≤ j.castSucc, v i = v 0) :
    (r.ray.truncate u).extend (r.parameter j.succ - u) (-r.parameter j.succ)
      (v 0) (by linarith) (by
        have := r.strictAnti_parameter (Fin.succ_pos j)
        rw [r.parameter_zero] at this
        linarith) = r.ray := by
  have hb : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  have hdir : r.ray.direction = v 0 := by
    simpa only [r.parameter_zero, FiniteAffineRay.directionAt_of_nonneg _ le_rfl] using
      r.directionAt_eq 0
  rw [← hdir]
  apply r.ray.extend_truncate hbefore hb
  intro a ha
  obtain ⟨k, rfl⟩ := r.bends_recorded a ha
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact Or.inl (hafter k hjk)
  · exact Or.inr rfl
  · have hsucc : k.succ ≤ j.castSucc := Fin.le_castSucc_iff.mpr
      (Fin.succ_lt_succ_iff.mpr hkj)
    have hcast : k.castSucc ≤ j.castSucc := k.castSucc_lt_succ.le.trans hsucc
    have hz : r.ray.bends (r.parameter k.succ) = 0 := by
      rw [r.bends_parameter, hv k.succ hsucc, hv k.castSucc hcast, sub_self]
    exact (Finsupp.mem_support_iff.mp ha hz).elim

end Mei.Convex.AdmissibleRayRealization
