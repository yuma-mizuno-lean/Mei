/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Terminal

/-!
# The final encounter of an admissible ray

A ray with at least one recorded encounter meets its final encounter, the one
nearest the endpoint, on the straight line through the endpoint in the final
direction. The encounter lies at positive distance, on its hyperplane and
in its selected support, and no wall support meets the open segment before it
(nor the endpoint itself). The encounter may leave the direction unchanged, and
the incoming tail is unrestricted.

We use `AdmissibleRayRealization.ray_eq_endpoint_sub_smul` for the straight
terminal segment and `AdmissibleRayRealization.parameter_eq_div_of_directions_eq`
for its length.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin (n + 1) → V →L[ℝ] ℝ} {c : Fin (n + 1) → ℝ}
  {v : Fin (n + 2) → V} {P : Fin (n + 1) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- The final encounter of a ray lies at a positive distance `τ` along the
backward line `Q + s • v 0`, on its hyperplane and in its support. The wall supports
miss the half-open segment `s ∈ [0, τ)` before it, including the endpoint. -/
theorem exists_finalEncounter (r : AdmissibleRayRealization f c v P W S C Q) :
    f 0 (v 0) ≠ 0 ∧ ∃ τ : ℝ, 0 < τ ∧ r.parameter (Fin.succ 0) = -τ ∧
      f 0 (Q + τ • v 0) = c 0 ∧ Q + τ • v 0 ∈ P 0 ∧
      ∀ a s, 0 ≤ s → s < τ → Q + s • v 0 ∉ W a := by
  have hv : ∀ i ≤ (0 : Fin (n + 1)).castSucc, v i = v 0 := fun i hi => by
    rw [Fin.le_zero_iff.mp hi]
  have hneg : r.parameter (Fin.succ 0) < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos 0)
  have htime : r.parameter (Fin.succ 0) = -((c 0 - f 0 Q) / f 0 (v 0)) := by
    rw [r.parameter_eq_div_of_directions_eq 0 hv, ← neg_div, neg_sub]
  have hpoint := r.ray_parameter_succ_eq_of_directions_eq 0 hv
  have htrans : f 0 (v 0) ≠ 0 := by
    simpa only [Fin.castSucc_zero] using r.transverse 0
  refine ⟨htrans, (c 0 - f 0 Q) / f 0 (v 0), ?_, htime, ?_, ?_, ?_⟩
  · linarith
  · simpa only [hpoint] using r.height_eq 0
  · simpa only [hpoint] using r.incidence 0
  · intro a s hs hlt
    rcases hs.eq_or_lt with rfl | hspos
    · simpa only [zero_smul, add_zero] using r.off_walls a
    have hτ : -s ∈ Icc (r.parameter (Fin.succ 0)) 0 :=
      ⟨by linarith, neg_nonpos.mpr hs⟩
    have hray : r.ray (-s) = Q + s • v 0 := by
      rw [r.ray_eq_endpoint_sub_smul (Fin.succ 0)
        (fun i hi => hv i (Fin.le_castSucc_iff.mpr hi)) hτ, neg_smul, sub_neg_eq_add]
    rw [← hray]
    refine r.avoids_walls a (-s) (neg_neg_of_pos hspos) fun j hj => ?_
    have hlt' : r.parameter (Fin.succ 0) < -s := by linarith
    exact (hj ▸ hlt').not_ge (r.strictAnti_parameter.antitone (Fin.succ_le_succ_iff.mpr
      (Fin.zero_le j)))

end Mei.Convex.AdmissibleRayRealization
