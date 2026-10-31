/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible

/-!
# Incoming segments of admissible rays

Between consecutive recorded encounters an admissible ray is affine in its
prescribed incoming direction. The same formula applies to the entire incoming
half-line before the earliest encounter. This identifies a cut just before an
encounter with a point on its incoming straight germ, retaining zero bends.

We use `FiniteAffineRay.eval_vsub_eval` and the recorded-encounter axioms of
`AdmissibleRayRealization`.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization


variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Before a recorded parameter and after every earlier encounter, the path is
the straight incoming germ in the prescribed direction. Both ends of a finite
segment are allowed, as is the unbounded incoming segment. -/
theorem ray_eq_add_smul_of_before_parameter
    (r : AdmissibleRayRealization f c v P W S C Q) (i : Fin (n + 1))
    {t : ℝ} (ht : t ≤ r.parameter i)
    (hafter : ∀ j, i < j → r.parameter j ≤ t) :
    r.ray t = r.ray (r.parameter i) + (r.parameter i - t) • v i := by
  have hb : ∀ b ∈ r.ray.bends.support, b ≤ t ∨ r.parameter i ≤ b := by
    intro b hb
    obtain ⟨j, rfl⟩ := r.bends_recorded b hb
    by_cases hj : i < j.succ
    · exact Or.inl (hafter j.succ hj)
    · exact Or.inr (r.strictAnti_parameter.antitone (le_of_not_gt hj))
  have he := r.ray.eval_vsub_eval ht hb
  rw [r.directionAt_eq, vsub_eq_sub] at he
  calc
    r.ray t = r.ray (r.parameter i) - (r.ray (r.parameter i) - r.ray t) := by abel
    _ = _ := by rw [he, ← neg_sub (r.parameter i) t, neg_smul, sub_neg_eq_add]

end Mei.Convex.AdmissibleRayRealization
