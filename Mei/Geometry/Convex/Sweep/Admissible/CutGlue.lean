/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Truncate
public import Mei.Geometry.Affine.FiniteRay.CutGlue

/-!
# Restoring an admissible ray after cutting its final encounter

Cut an admissible ray in the open segment immediately before its final encounter.
Reattaching that encounter with its original two segment lengths and final direction
recovers the entire finite ray. Every earlier encounter and the incoming tail are
therefore preserved, including when the discarded encounter has unchanged direction.

This is the geometric inverse law for cutting decorated broken lines at a last
degree change, as in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5). The proof uses the recorded-bend
axiom of `AdmissibleRayRealization` and `FiniteAffineRay.extend_truncate`.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

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
  exact r.ray.extend_truncate hupper (by
    simpa only [r.parameter_zero] using
      r.strictAnti_parameter (a := 0) (b := Fin.natAdd 1 (0 : Fin (n + 1)))
        (by simp [Fin.lt_def]))
    (r.bends_before_cut_or_final a hlower)

end Mei.Convex.AdmissibleRayRealization
