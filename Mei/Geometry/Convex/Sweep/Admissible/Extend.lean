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
  (s t : ℝ) (w : V) (hs : 0 ≤ s) (ht : 0 < t)

private theorem parameter_succ_neg (j : Fin n) : r.parameter j.succ < 0 := by
  simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)

include hs ht in
private theorem strictAnti_extend_parameter :
    StrictAnti (Fin.cons 0 (Fin.cons (-t) (fun j => r.parameter j.succ - (s + t)))) := by
  apply (Fin.liftFun_cons (fun a b : ℝ => b < a)).mpr
  refine ⟨?_, (Fin.liftFun_cons (fun a b : ℝ => b < a)).mpr ⟨?_, ?_⟩⟩
  · intro j
    cases j using Fin.cases with
    | zero => simpa using neg_neg_of_pos ht
    | succ j => simp only [Fin.cons_succ]; linarith [r.parameter_succ_neg j]
  · intro j
    linarith [r.parameter_succ_neg j]
  · intro i j hij
    dsimp
    linarith [r.strictAnti_parameter (Fin.succ_lt_succ_iff.mpr hij)]

private theorem extend_apply_parameter (j : Fin (n + 1)) :
    r.ray.extend s t w hs ht
        ((Fin.cons (-t) (fun j => r.parameter j.succ - (s + t)) : Fin (n + 1) → ℝ) j) =
      (Fin.cons (r.ray s) (fun j => r.ray (r.parameter j.succ)) : Fin (n + 1) → V) j := by
  cases j using Fin.cases with
  | zero =>
    simpa using r.ray.extend_apply_of_le s t w hs ht (le_refl (-t))
  | succ j =>
    exact r.ray.extend_apply_sub s t w hs ht (r.parameter_succ_neg j).le

-- A time-dependent property of the extension follows from its three pieces:
-- the old half-line, the continuation of the old final segment, and the new segment.
private theorem forall_extend_of_segments (F : ℝ → V → Prop)
    (hOld : ∀ a, a ≤ 0 → F (a - (s + t)) (r.ray a))
    (h₁ : ∀ a, 0 < a → a ≤ s → F (a - (s + t)) (r.ray a))
    (h₂ : ∀ u, -t < u → u ≤ 0 →
      F u ((-u • w) +ᵥ (r.ray.extend s t w hs ht).endpoint)) :
    ∀ u, u ≤ 0 → F u (r.ray.extend s t w hs ht u) := by
  intro u hu
  by_cases hbefore : u ≤ -t
  · rw [FiniteAffineRay.extend_apply_of_le _ _ _ _ hs ht hbefore]
    by_cases hold : u + (s + t) ≤ 0
    · simpa using hOld (u + (s + t)) hold
    · simpa using h₁ (u + (s + t)) (lt_of_not_ge hold) (by linarith)
  · rw [FiniteAffineRay.extend_apply_of_ge _ _ _ _ hs ht (le_of_not_ge hbefore)]
    exact h₂ u (lt_of_not_ge hbefore) hu

/-- Attach an encounter after continuing the old final segment for nonnegative
time `s`, and then continue for positive time `t` in direction `w`. The hypotheses
check incidence and avoidance only on the newly attached segments. -/
def extend (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
    (htrans : m w ≠ 0) (hheight : m (r.ray s) = b) (hinc : r.ray s ∈ H)
    (hW₁ : ∀ a u, 0 < u → u < s → r.ray u ∉ W a)
    (hW₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs ht).endpoint ∉ W a)
    (hS₁ : ∀ a u, 0 < u → u ≤ s → r.ray u ∉ S a)
    (hS₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs ht).endpoint ∉ S a) :
    AdmissibleRayRealization (Fin.cons m f) (Fin.cons b c) (Fin.cons w v)
      (Fin.cons H P) W S C (r.ray.extend s t w hs ht).endpoint := by
  classical
  let τ : Fin (n + 2) → ℝ :=
    Fin.cons 0 (Fin.cons (-t) (fun j => r.parameter j.succ - (s + t)))
  have hdir : r.ray.directionAt s = v 0 := by
    rw [← r.directionAt_eq 0, r.parameter_zero]
    rw [r.ray.directionAt_of_nonneg hs, r.ray.directionAt_of_nonneg le_rfl]
  -- Translate every old encounter and put the new encounter before the endpoint.
  refine {
    ray := r.ray.extend s t w hs ht
    parameter := τ
    parameter_zero := by simp [τ]
    strictAnti_parameter := r.strictAnti_extend_parameter s t hs ht
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
  -- The new normal is transverse to the new direction; old pairs are unchanged.
  · intro j
    cases j using Fin.cases with
    | zero => simpa using htrans
    | succ j => simpa using r.transverse j
  -- At the endpoint use the new direction; at encounters retain the old directions.
  · intro j
    cases j using Fin.cases with
    | zero => simp [τ]
    | succ j =>
      cases j using Fin.cases with
      | zero =>
        simpa [τ] using
          (r.ray.directionAt_extend_of_le s t w hs ht (le_refl (-t))).trans
            (by simpa using hdir)
      | succ j =>
        have he := r.ray.directionAt_extend_of_le s t w hs ht
          (by linarith [r.parameter_succ_neg j] : r.parameter j.succ - (s + t) ≤ -t)
        simpa [τ] using he.trans (by simpa using r.directionAt_eq j.succ)
  -- Every bend is either a translated old bend or the new recorded encounter.
  · intro u hu
    rcases r.ray.mem_support_bends_extend s t w hs ht hu with ⟨a, ha, rfl⟩ | rfl
    · obtain ⟨j, rfl⟩ := r.bends_recorded a ha
      exact ⟨j.succ, by simp [τ]⟩
    · exact ⟨0, by simp [τ]⟩
  -- The encounter values give the new height followed by all old heights.
  · intro j
    simp only [τ, Fin.cons_succ]
    rw [r.extend_apply_parameter s t w hs ht j]
    exact Fin.cases hheight r.height_eq j
  -- The same encounter values preserve membership in the selected supports.
  · intro j
    simp only [τ, Fin.cons_succ]
    rw [r.extend_apply_parameter s t w hs ht j]
    exact Fin.cases hinc r.incidence j
  -- Wall avoidance excludes recorded times; in particular the new encounter.
  · intro a u hu hnot
    apply r.forall_extend_of_segments s t w hs ht
      (fun z x => (∀ j : Fin (n + 1), z ≠ τ j.succ) → x ∉ W a) ?_ ?_ ?_ u hu.le hnot
    · intro z hz hn
      by_cases hz₀ : z < 0
      · apply r.avoids_walls a z hz₀
        intro j he
        exact hn j.succ (by simp [τ, he])
      · have he : z = 0 := le_antisymm hz (le_of_not_gt hz₀)
        subst z
        simpa [r.endpoint_eq] using r.off_walls a
    · intro z hz hzs hn
      have hne : z ≠ s := by
        intro he
        subst z
        exact hn 0 (by simp [τ])
      exact hW₁ a z hz (lt_of_le_of_ne hzs hne)
    · intro z hz hz₀ _
      exact hW₂ a z hz hz₀
  -- A translated sufficiently negative time remains in the admitted incoming tail.
  · obtain ⟨a, ha⟩ := eventually_atBot.mp r.incoming
    filter_upwards [eventually_le_atBot (min (-t) (a - (s + t)))] with u hu
    rw [FiniteAffineRay.extend_apply_of_le _ _ _ _ hs ht (hu.trans (min_le_left _ _))]
    exact ha _ (by linarith [hu.trans (min_le_right (-t) (a - (s + t)))])
  -- Singular avoidance includes encounter times and the endpoint.
  · intro a
    exact r.forall_extend_of_segments s t w hs ht (fun _ x => x ∉ S a)
      (r.avoids_singular a) (hS₁ a) (hS₂ a)
  -- The new endpoint lies on the second attached segment.
  · intro a
    simpa using hW₂ a 0 (by linarith) le_rfl

variable (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
  (htrans : m w ≠ 0) (hheight : m (r.ray s) = b) (hinc : r.ray s ∈ H)
  (hW₁ : ∀ a u, 0 < u → u < s → r.ray u ∉ W a)
  (hW₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs ht).endpoint ∉ W a)
  (hS₁ : ∀ a u, 0 < u → u ≤ s → r.ray u ∉ S a)
  (hS₂ : ∀ a u, -t < u → u ≤ 0 → (-u • w) +ᵥ (r.ray.extend s t w hs ht).endpoint ∉ S a)

/-- The admissible extension uses the finite-ray attachment, so its full path,
bend increments and incoming direction are given by that operation's equations. -/
@[simp]
theorem ray_extend :
    (r.extend s t w hs ht m b H htrans hheight hinc hW₁ hW₂ hS₁ hS₂).ray =
      r.ray.extend s t w hs ht := (rfl)

/-- The new encounter is at `-t`; all old encounters are translated by `s + t`.
The leading parameter remains the endpoint at time zero. -/
@[simp]
theorem parameter_extend :
    (r.extend s t w hs ht m b H htrans hheight hinc hW₁ hW₂ hS₁ hS₂).parameter =
      Fin.cons 0 (Fin.cons (-t) (fun j => r.parameter j.succ - (s + t))) := (rfl)

end Mei.Convex.AdmissibleRayRealization
