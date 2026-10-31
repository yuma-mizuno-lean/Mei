/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible

/-!
# Straight terminal pieces of admissible rays

If all recorded directions between an encounter and the endpoint agree, that
whole closed terminal interval is straight. Encounters with zero bend remain
recorded. This lets a last change of coefficient degree determine a terminal
piece even when that change has zero spatial projection.

We use `AdmissibleRayRealization.bends_parameter` to exclude actual bends and
`FiniteAffineRay.eval_vsub_eval` to recover the path on the interval.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Equal recorded directions give the straight formula on the entire closed
terminal interval, including its initial encounter and the endpoint. Only
directions strictly after the initial encounter must agree; its incoming
direction is unrestricted. -/
theorem ray_eq_endpoint_sub_smul
    (r : AdmissibleRayRealization f c v P W S C Q) (j : Fin (n + 1))
    (hv : ∀ i < j, v i = v 0) {t : ℝ} (ht : t ∈ Icc (r.parameter j) 0) :
    r.ray t = Q - t • v 0 := by
  have hb : ∀ b ∈ r.ray.bends.support, b ≤ r.parameter j := by
    intro b hb
    obtain ⟨i, rfl⟩ := r.bends_recorded b hb
    by_contra hn
    have hi : i.succ < j := by
      by_contra hi
      exact hn (r.strictAnti_parameter.antitone (le_of_not_gt hi))
    have hz : r.ray.bends (r.parameter i.succ) = 0 := by
      rw [r.bends_parameter, hv i.succ hi,
        hv i.castSucc (i.castSucc_lt_succ.trans hi), sub_self]
    exact (Finsupp.mem_support_iff.mp hb) hz
  have he := r.ray.eval_vsub_eval ht.2 (fun b hb' => Or.inl ((hb b hb').trans ht.1))
  rw [← r.parameter_zero, r.directionAt_eq] at he
  simp only [r.parameter_zero, FiniteAffineRay.eval_zero, r.endpoint_eq, vsub_eq_sub,
    sub_zero] at he
  exact (eq_sub_iff_add_eq').mpr (sub_eq_iff_eq_add.mp he).symm

/-- If all recorded directions agree, the entire negative half-line is straight.
This includes constant rays and itineraries with no encounters. -/
theorem ray_eq_endpoint_sub_smul_of_directions_eq
    (r : AdmissibleRayRealization f c v P W S C Q)
    (hv : ∀ i, v i = v 0) {t : ℝ} (ht : t ≤ 0) :
    r.ray t = Q - t • v 0 := by
  have hb : ∀ b, b ∉ r.ray.bends.support := by
    intro b hb
    obtain ⟨i, rfl⟩ := r.bends_recorded b hb
    apply Finsupp.mem_support_iff.mp hb
    rw [r.bends_parameter, hv i.succ, hv i.castSucc, sub_self]
  have he := r.ray.eval_vsub_eval ht (fun b hb' => (hb b hb').elim)
  rw [← r.parameter_zero, r.directionAt_eq] at he
  simp only [r.parameter_zero, FiniteAffineRay.eval_zero, r.endpoint_eq, vsub_eq_sub,
    sub_zero] at he
  exact (eq_sub_iff_add_eq').mpr (sub_eq_iff_eq_add.mp he).symm

/-- If the terminal piece is straight, its initial encounter parameter is the
intersection parameter of that straight line with the encounter hyperplane.
All later encounters, including those with zero bend, are allowed. -/
theorem parameter_eq_div_of_directions_eq
    (r : AdmissibleRayRealization f c v P W S C Q) (j : Fin n)
    (hv : ∀ i ≤ j.castSucc, v i = v 0) :
    r.parameter j.succ = (f j Q - c j) / f j (v 0) := by
  have ht : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  have hp := r.ray_eq_endpoint_sub_smul j.succ
    (fun i hi => hv i (Fin.le_castSucc_iff.mpr hi)) ⟨le_rfl, ht.le⟩
  have he := r.height_eq j
  rw [hp, map_sub, map_smul, smul_eq_mul] at he
  have hn : f j (v 0) ≠ 0 := by
    simpa only [hv j.castSucc le_rfl] using r.transverse j
  apply (eq_div_iff hn).mpr
  linarith

end Mei.Convex.AdmissibleRayRealization
