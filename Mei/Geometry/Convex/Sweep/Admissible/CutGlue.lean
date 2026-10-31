/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Truncate
public import Mei.Geometry.Affine.FiniteRay.CutGlue

/-!
# Restoring admissible rays after incoming cuts

Cut an admissible ray in the open segment immediately before its final encounter.
Reattaching that encounter with its original two segment lengths and final direction
recovers the entire finite ray. Every earlier encounter and the incoming tail are
therefore preserved, including when the discarded encounter has unchanged direction.
More generally, `ray_extend_truncate` reconstructs the path at or before any selected
encounter followed only by unchanged directions. Later recorded encounters are
allowed: their equal adjacent directions force their bend increments to vanish.
This generalization uses `AdmissibleRayRealization.bends_parameter`.

This is the geometric inverse law for cutting decorated broken lines at a last
degree change, as in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5). The proof uses the recorded-bend
axiom of `AdmissibleRayRealization` and `FiniteAffineRay.extend_truncate`.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

section GeneralEncounter

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Reattach an incoming cut at or before an encounter followed only by unchanged
directions. Recover the full path, including every earlier bend and the entire
incoming half-line. No nonzero bend at the chosen encounter is required. -/
theorem ray_extend_truncate (r : AdmissibleRayRealization f c v P W S C Q)
    (j : Fin n) {u : ℝ} (hbefore : u ≤ r.parameter j.succ)
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

end GeneralEncounter

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin (1 + n) → V →L[ℝ] ℝ} {c : Fin (1 + n) → ℝ}
  {v : Fin (1 + n + 1) → V} {P : Fin (1 + n) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization f c v P W S C Q)
  (a : ℝ)
  (hupper : a < r.parameter (Fin.natAdd 1 (0 : Fin (n + 1))))
  (hlower : ∀ j : Fin n, r.parameter (Fin.natAdd 1 j).succ < a)

include hlower in
private theorem bends_before_cut_or_final :
    ∀ u ∈ r.ray.bends.support,
      u < a ∨ u = r.parameter (Fin.natAdd 1 (0 : Fin (n + 1))) := by
  intro u hu
  obtain ⟨j, rfl⟩ := r.bends_recorded u hu
  by_cases hj : j.val = 0
  · right
    congr 1
    apply Fin.ext
    simp [hj]
  · left
    let k : Fin n := ⟨j.val - 1, by omega⟩
    have he : j = Fin.natAdd 1 k := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      dsimp [k]
      omega
    simpa only [he] using hlower k

/-- Reattaching the final encounter to its actual incoming truncation restores
the full ray. The only cut hypotheses place the cut in the preceding open segment;
the recorded-encounter axioms supply the required absence of other bends. -/
@[simp↓]
theorem extend_truncate_ray :
    (r.truncate a hupper hlower).ray.extend
      (r.parameter (Fin.natAdd 1 (0 : Fin (n + 1))) - a)
      (-r.parameter (Fin.natAdd 1 (0 : Fin (n + 1)))) (v 0)
      (sub_nonneg.mpr hupper.le) (neg_pos.mpr (by
        simpa only [r.parameter_zero] using
          r.strictAnti_parameter (a := 0) (b := Fin.natAdd 1 (0 : Fin (n + 1)))
            (by simp [Fin.lt_def]))) =
        r.ray := by
  have hdir : r.ray.direction = v 0 := by
    simpa only [r.parameter_zero, FiniteAffineRay.directionAt_of_nonneg _ le_rfl] using
      r.directionAt_eq 0
  rw [ray_truncate, ← hdir]
  exact r.ray.extend_truncate hupper.le (by
    simpa only [r.parameter_zero] using
      r.strictAnti_parameter (a := 0) (b := Fin.natAdd 1 (0 : Fin (n + 1)))
        (by simp [Fin.lt_def]))
    (r.bends_before_cut_or_final a hlower)

end Mei.Convex.AdmissibleRayRealization
