/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Affine.FiniteRay.Extend
import Mathlib.Order.Fin.Tuple

/-!
# Attaching a final encounter to an admissible ray

An incoming ray ending off the walls can be continued along its final straight
segment to a transverse encounter, then along a new direction to a new endpoint.
Checking wall and singular avoidance only on the two attached finite segments
suffices: the entire old negative half-line and its source admission are retained.
The new encounter is recorded even when the spatial direction does not change.
Coefficient propagation and conservation of normal velocity are separate conditions.

This is the geometric reconstruction in the last-encounter recursion for
broken lines; see Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5). The construction combines
`FiniteAffineRay.extend` with `AdmissibleRayRealization`'s local encounter data.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set Filter

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization f c v P W S C Q)
  (s t : ℝ) (w : V) (hs : 0 < s) (ht : 0 < t)

/-- Attach an encounter after continuing the old final segment for positive
time `s`, and then continue for positive time `t` in direction `w`. The hypotheses
check incidence and avoidance only on the newly attached segments. -/
def extend (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
    (htrans : m w ≠ 0) (hheight : m (r.ray s) = b) (hinc : r.ray s ∈ H)
    (hW₁ : ∀ a u, 0 ≤ u → u < s → r.ray u ∉ W a)
    (hW₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs.le ht).endpoint ∉ W a)
    (hS₁ : ∀ a u, 0 ≤ u → u ≤ s → r.ray u ∉ S a)
    (hS₂ : ∀ a u, -t ≤ u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs.le ht).endpoint ∉ S a) :
    AdmissibleRayRealization (Fin.cons m f) (Fin.cons b c) (Fin.cons w v)
      (Fin.cons H P) W S C (r.ray.extend s t w hs.le ht).endpoint := by
  classical
  let τ : Fin (n + 2) → ℝ :=
    Fin.cons 0 (Fin.cons (-t) (fun j => r.parameter j.succ - (s + t)))
  have hp (j : Fin n) : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  have hdir : r.ray.directionAt s = v 0 := by
    rw [← r.directionAt_eq 0, r.parameter_zero]
    simp only [FiniteAffineRay.directionAt_def]
    congr 1
    apply Finsupp.sum_congr
    intro a ha
    have hn := r.ray.bend_neg a ha
    simp [hn.not_ge, (hn.trans hs).not_ge]
  -- Translate every old encounter and put the new encounter before the endpoint.
  refine {
    ray := r.ray.extend s t w hs.le ht
    parameter := τ
    parameter_zero := by simp [τ]
    strictAnti_parameter := ?_
    transverse := ?_
    endpoint_eq := rfl
    directionAt_eq := ?_
    bends_recorded := ?_
    height_eq := ?_
    incidence := ?_
    avoids_walls := ?_
    incoming := ?_
    avoids_singular := ?_
    off_walls := ?_ }
  · apply (Fin.liftFun_cons (fun a b : ℝ => b < a)).mpr
    refine ⟨?_, (Fin.liftFun_cons (fun a b : ℝ => b < a)).mpr ⟨?_, ?_⟩⟩
    · intro j
      cases j using Fin.cases with
      | zero => simpa using neg_neg_of_pos ht
      | succ j => simp only [Fin.cons_succ]; linarith [hp j]
    · intro j
      linarith [hp j]
    · intro i j hij
      dsimp
      linarith [r.strictAnti_parameter (Fin.succ_lt_succ_iff.mpr hij)]
  · intro j
    cases j using Fin.cases with
    | zero => simpa using htrans
    | succ j => simpa using r.transverse j
  · intro j
    cases j using Fin.cases with
    | zero => simpa [τ] using
        r.ray.directionAt_extend_of_gt s t w hs.le ht (by linarith : -t < 0)
    | succ j =>
      cases j using Fin.cases with
      | zero =>
        simpa [τ] using
          (r.ray.directionAt_extend_of_le s t w hs.le ht (le_refl (-t))).trans
            (by simpa using hdir)
      | succ j =>
        have he := r.ray.directionAt_extend_of_le s t w hs.le ht
          (by linarith [hp j] : r.parameter j.succ - (s + t) ≤ -t)
        simpa [τ] using he.trans (by simpa using r.directionAt_eq j.succ)
  · intro u hu
    rw [FiniteAffineRay.bends_extend] at hu
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · rw [Finsupp.mapDomain_support_of_injective
        (fun _ _ h => sub_left_injective h)] at hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, rfl⟩ := r.bends_recorded a ha
      exact ⟨j.succ, by simp [τ]⟩
    · exact ⟨0, by simpa [τ] using
        Finset.mem_singleton.mp (Finsupp.support_single_subset hu)⟩
  · intro j
    cases j using Fin.cases with
    | zero =>
      simpa [τ, FiniteAffineRay.extend_apply_of_le _ _ _ _ hs.le ht (le_refl (-t))]
        using hheight
    | succ j =>
      simpa [τ, FiniteAffineRay.extend_apply_sub _ _ _ _ hs.le ht (hp j).le]
        using r.height_eq j
  · intro j
    cases j using Fin.cases with
    | zero =>
      simpa [τ, FiniteAffineRay.extend_apply_of_le _ _ _ _ hs.le ht (le_refl (-t))]
        using hinc
    | succ j =>
      simpa [τ, FiniteAffineRay.extend_apply_sub _ _ _ _ hs.le ht (hp j).le]
        using r.incidence j
  -- On the old half-line reuse admissibility; check only the attached intervals.
  · intro a u hu hnot
    by_cases hbefore : u ≤ -t
    · rw [FiniteAffineRay.extend_apply_of_le _ _ _ _ hs.le ht hbefore]
      have hne : u ≠ -t := by simpa [τ] using hnot 0
      by_cases hold : u + (s + t) < 0
      · apply r.avoids_walls a _ hold
        intro j he
        apply hnot j.succ
        simpa [τ] using (eq_sub_iff_add_eq.mpr he)
      · exact hW₁ a _ (le_of_not_gt hold) (by
          have hlt : u < -t := lt_of_le_of_ne hbefore hne
          linarith)
    · rw [FiniteAffineRay.extend_apply_of_ge _ _ _ _ hs.le ht (le_of_not_ge hbefore)]
      exact hW₂ a u (lt_of_not_ge hbefore) hu.le
  · obtain ⟨a, ha⟩ := eventually_atBot.mp r.incoming
    filter_upwards [eventually_le_atBot (min (-t) (a - (s + t)))] with u hu
    rw [FiniteAffineRay.extend_apply_of_le _ _ _ _ hs.le ht (hu.trans (min_le_left _ _))]
    exact ha _ (by linarith [hu.trans (min_le_right (-t) (a - (s + t)))])
  · intro a u hu
    by_cases hbefore : u ≤ -t
    · rw [FiniteAffineRay.extend_apply_of_le _ _ _ _ hs.le ht hbefore]
      by_cases hold : u + (s + t) ≤ 0
      · exact r.avoids_singular a _ hold
      · exact hS₁ a _ (le_of_not_ge hold) (by linarith)
    · rw [FiniteAffineRay.extend_apply_of_ge _ _ _ _ hs.le ht (le_of_not_ge hbefore)]
      exact hS₂ a u (le_of_not_ge hbefore) hu
  · intro a
    simpa using hW₂ a 0 (by linarith) le_rfl

variable (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
  (htrans : m w ≠ 0) (hheight : m (r.ray s) = b) (hinc : r.ray s ∈ H)
  (hW₁ : ∀ a u, 0 ≤ u → u < s → r.ray u ∉ W a)
  (hW₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs.le ht).endpoint ∉ W a)
  (hS₁ : ∀ a u, 0 ≤ u → u ≤ s → r.ray u ∉ S a)
  (hS₂ : ∀ a u, -t ≤ u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs.le ht).endpoint ∉ S a)

/-- The admissible extension uses the finite-ray attachment, so its full path,
bend increments and incoming direction are given by that operation's equations. -/
@[simp]
theorem ray_extend :
    (r.extend s t w hs ht m b H htrans hheight hinc hW₁ hW₂ hS₁ hS₂).ray =
      r.ray.extend s t w hs.le ht := (rfl)

/-- The new encounter is at `-t`; all old encounters are translated by `s + t`.
The leading parameter remains the endpoint at time zero. -/
@[simp]
theorem parameter_extend :
    (r.extend s t w hs ht m b H htrans hheight hinc hW₁ hW₂ hS₁ hS₂).parameter =
      Fin.cons 0 (Fin.cons (-t) (fun j => r.parameter j.succ - (s + t))) := (rfl)

end Mei.Convex.AdmissibleRayRealization
