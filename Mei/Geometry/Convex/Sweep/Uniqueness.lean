/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization

/-!
# Recovering finite rays from transverse itineraries

An arbitrary finite affine ray with a specified sequence of transverse
hyperplane encounters is the backward realization of that itinerary. The
encounter parameters and positions are recovered from its endpoint, normals,
levels and segment directions. No genericity assumption on the endpoint is
needed. Encounters with unchanged direction are retained, and the incoming
segment may have zero direction.

The hypotheses describe the actual ray: its possible bends lie among the
strictly ordered encounter parameters, its incoming direction at each parameter
is specified, and its encounter points lie on the selected hyperplanes. They
do not prescribe the backward formulas or the bend increments. Those follow
from `backward_unique`, `FiniteAffineRay.eval_vsub_eval` and the jump of
`FiniteAffineRay.directionAt` across an interval without interior bends.
This is the geometric uniqueness used to parameterize a transverse broken-line
type by its endpoint; avoidance, incoming admission and coefficient propagation
can impose further restrictions on the endpoint domain.

The backward parameterization follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (β : FiniteAffineRay V V) (t : Fin (n + 1) → ℝ)
  (ht : StrictAnti t)
  (hb : ∀ s ∈ β.bends.support, ∃ j : Fin n, s = t j.succ)

include ht hb in
omit [NormedSpace ℝ V] in
private theorem bends_outside_encounter_interval (j : Fin n) :
    ∀ s ∈ β.bends.support, s ≤ t j.succ ∨ t j.castSucc ≤ s := by
  intro s hs
  obtain ⟨a, rfl⟩ := hb s hs
  by_cases hja : j ≤ a
  · exact Or.inl (ht.antitone (Fin.succ_le_succ_iff.mpr hja))
  · apply Or.inr
    apply ht.antitone
    simpa only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] using
      Nat.succ_le_iff.mpr (lt_of_not_ge hja)

variable (h0 : t 0 = 0) (hv : ∀ j, β.directionAt (t j) = v j)
  (hf : ∀ j, f j (v j.castSucc) ≠ 0)
  (hheight : ∀ j, f j (β (t j.succ)) = c j)

include ht hb h0 hv hf hheight in
/-- Actual transverse encounters recover both the affine encounter positions
and their cumulative parameters, without prescribing either backward formula. -/
theorem backward_eq_of_ray_encounters :
    (∀ j, β (t j) = backwardPoint f c (fun j => v j.castSucc) j β.endpoint) ∧
      ∀ j, t j = backwardParameter f c (fun j => v j.castSucc) j β.endpoint := by
  have hstep (j : Fin n) :
      β (t j.succ) = β (t j.castSucc) + (t j.castSucc - t j.succ) • v j.castSucc := by
    have he := β.eval_vsub_eval (ht Fin.castSucc_lt_succ).le
      (bends_outside_encounter_interval β t ht hb j)
    -- Vector subtraction on the affine space over itself is ordinary subtraction.
    rw [hv, vsub_eq_sub] at he
    calc
      _ = β (t j.castSucc) - (β (t j.castSucc) - β (t j.succ)) := by abel
      _ = β (t j.castSucc) - (t j.succ - t j.castSucc) • v j.castSucc := by rw [he]
      _ = _ := by module
  have hrec := backward_unique f c (fun j => v j.castSucc) hf β.endpoint
    (fun j => β (t j)) (fun j => t j.castSucc - t j.succ)
    (by simp [h0]) hstep hheight
  refine ⟨hrec.1, ?_⟩
  intro j
  induction j using Fin.induction with
  | zero => simpa using h0
  | succ j ih =>
    rw [backwardParameter_succ, ← ih, ← hrec.2 j]
    abel

include ht hb h0 hv hf hheight in
/-- Endpoint and a transverse itinerary determine the entire finite affine ray.
Positive backward elapsed times are a consequence of the actual encounter order.
Unchanged directions need not be removed from the itinerary. -/
theorem eq_backwardRay_of_encounters :
    ∃ hpos : ∀ j,
        0 < backwardTime f c (fun j => v j.castSucc) j β.endpoint,
      (∀ j, t j = backwardParameter f c (fun j => v j.castSucc) j β.endpoint) ∧
        β = backwardRay f c v β.endpoint hpos := by
  classical
  have hparameter := (backward_eq_of_ray_encounters f c v β t ht hb h0 hv hf hheight).2
  have hpos (j : Fin n) :
      0 < backwardTime f c (fun j => v j.castSucc) j β.endpoint := by
    have he := hparameter j.succ
    rw [backwardParameter_succ, ← hparameter j.castSucc] at he
    linarith [ht (Fin.castSucc_lt_succ (i := j))]
  refine ⟨hpos, hparameter, ?_⟩
  have hjump (j : Fin n) : β.bends (t j.succ) = v j.succ - v j.castSucc := by
    rw [← β.directionAt_sub_eq_bends (ht Fin.castSucc_lt_succ)
      (bends_outside_encounter_interval β t ht hb j), hv, hv]
  have hbends : β.bends =
      ∑ j : Fin n, Finsupp.single (t j.succ) (v j.succ - v j.castSucc) := by
    ext s
    simp only [Finsupp.finsetSum_apply]
    by_cases hs : ∃ j : Fin n, s = t j.succ
    · obtain ⟨j, rfl⟩ := hs
      rw [Finset.sum_eq_single j]
      · simp [hjump]
      · intro a _ haj
        exact Finsupp.single_eq_of_ne (fun he => haj
          (Fin.succ_injective _ (ht.injective he.symm)))
      · simp
    · have hnot : s ∉ β.bends.support := fun h => hs (hb s h)
      rw [Finsupp.notMem_support_iff.mp hnot]
      symm
      apply Finset.sum_eq_zero
      intro j _
      exact Finsupp.single_eq_of_ne (fun he => hs ⟨j, he⟩)
  apply FiniteAffineRay.ext
  · simp
  · rw [direction_backwardRay, ← hv 0, h0, FiniteAffineRay.directionAt_def]
    have hz : β.bends.sum (fun b w => if 0 ≤ b then w else 0) = 0 := by
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro b hb'
      exact ite_eq_right (β.bend_neg b hb').not_ge
    rw [hz, add_zero]
  · rw [bends_backwardRay, hbends]
    apply Finset.sum_congr rfl
    intro j _
    rw [hparameter]

end Mei.Convex
