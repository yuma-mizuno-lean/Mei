/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Affine.FiniteRay.Truncate
public import Mei.Data.Fin.Tuple

/-!
# Continuing an admissible ray through a straight encounter block

Continue the final segment of an admissible ray, recording every prescribed
transverse encounter on the added segment. The new encounters need not be bends.
Only the added segment needs incidence and avoidance checks; the entire earlier
path and its incoming source are retained.

The construction uses `FiniteAffineRay.truncate` at a nonnegative parameter to
translate the endpoint forwards. It supplies the unchanged-direction terminal
blocks in the last-change recursion for broken lines, following Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set Filter

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Y : V}
  (r : AdmissibleRayRealization f c v P W S C Y)
  (L : ℝ) (hL : 0 ≤ L) (τ : Fin m → ℝ)
  (hτ : StrictAnti τ) (hpos : ∀ j, 0 < τ j) (hlt : ∀ j, τ j < L)
  (g : Fin m → V →L[ℝ] ℝ) (b : Fin m → ℝ) (H : Fin m → Set V)
  (htrans : ∀ j, g j (v 0) ≠ 0)
  (hheight : ∀ j, g j (Y - τ j • v 0) = b j)
  (hinc : ∀ j, Y - τ j • v 0 ∈ H j)
  (hW : ∀ a u, 0 < u → u ≤ L → (∀ j, u ≠ τ j) → Y - u • v 0 ∉ W a)
  (hS : ∀ a u, 0 < u → u ≤ L → Y - u • v 0 ∉ S a)

/-- Continue along the final direction for time `L`, recording a complete
straight block of transverse encounters at the positive times `τ`. The earlier
ray, its encounters and its source admission are preserved. Empty added blocks
and zero continuation length are allowed. -/
def continueStraight :
    AdmissibleRayRealization (Fin.append g f) (Fin.append b c)
      (Fin.append (m := m) (n := n + 1) (fun _ : Fin m => v 0) v)
      (Fin.append H P) W S C (Y - L • v 0) := by
  classical
  let σ : Fin (m + n + 1) → ℝ :=
    Fin.cons 0 (Fin.append (fun j => τ j - L) (fun j => r.parameter j.succ - L))
  have hneg (j : Fin n) : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  have hparamNew (j : Fin m) : σ (Fin.castAdd n j).succ = τ j - L := by
    simp [σ]
  have hparamOld (j : Fin n) : σ (Fin.natAdd m j).succ = r.parameter j.succ - L := by
    simp [σ]
  have hvelNew (j : Fin m) :
      Fin.append (fun _ : Fin m => v 0) v (Fin.castAdd n j).succ = v 0 := by
    rw [← Fin.snoc_init_self v, Fin.append_snoc, Fin.snoc_append_castAdd_succ]
    simp [Fin.snoc]
  have hvelOld (j : Fin n) :
      Fin.append (fun _ : Fin m => v 0) v (Fin.natAdd m j).succ = v j.succ := by
    rw [Fin.succ_natAdd, Fin.append_right]
  have hvelZero : Fin.append (fun _ : Fin m => v 0) v 0 = v 0 := by
    cases m <;> simp [Fin.append, Fin.addCases]
  have hvalue {u : ℝ} (hu : 0 ≤ u) : r.ray u = Y - u • v 0 := by
    simpa only [neg_smul, vadd_eq_add, sub_eq_add_neg, add_comm] using r.ray_of_nonneg hu
  -- Translate the old ray and every encounter time. Check each field on the
  -- old half-line or on the newly added straight segment, separated at time `-L`.
  refine {
    ray := r.ray.truncate L
    parameter := σ
    parameter_zero := by simp [σ]
    strictAnti_parameter := ?_
    transverse := ?_
    endpoint_eq := by simp only [FiniteAffineRay.endpoint_truncate, hvalue hL]
    directionAt_eq := ?_
    bends_recorded := ?_
    height_eq := ?_
    incidence := ?_
    avoids_walls := ?_
    incoming := (FiniteAffineRay.eventually_truncate_mem_iff _ _ _).mpr r.incoming
    avoids_singular := ?_
    off_walls := ?_ }
  · apply (Fin.liftFun_cons (fun a b : ℝ => b < a)).mpr
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using sub_neg.mpr (hlt j)
      · simp only [Fin.append_right]
        linarith [hneg j]
    · intro i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · intro hij
          simp only [Fin.append_left]
          linarith [hτ (by simpa only [Fin.lt_def, Fin.val_castAdd] using hij)]
        · intro _
          simp only [Fin.append_left, Fin.append_right]
          linarith [hneg j, hpos i]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · intro hij
          have := i.isLt
          have := j.isLt
          simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij
          omega
        · intro hij
          simp only [Fin.append_right]
          have hij' : i.succ < j.succ := by
            simpa only [Fin.lt_def, Fin.val_succ, Fin.val_natAdd,
              Nat.add_lt_add_iff_left, Nat.add_lt_add_iff_right] using hij
          linarith [r.strictAnti_parameter hij']
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left, Fin.castSucc_castAdd] using htrans j
    · simpa only [Fin.append_right, Fin.castSucc_natAdd] using r.transverse j
  · intro j
    cases j using Fin.cases with
    | zero => simp [σ, hvelZero, FiniteAffineRay.directionAt_of_nonneg, hL]
    | succ j =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [hparamNew, FiniteAffineRay.directionAt_truncate _ _ (sub_nonpos.mpr (hlt j).le),
          sub_add_cancel, FiniteAffineRay.directionAt_of_nonneg _ (hpos j).le,
          r.ray_direction, hvelNew]
      · rw [hparamOld, FiniteAffineRay.directionAt_truncate _ _ (by linarith [hneg j]),
          sub_add_cancel, r.directionAt_eq, hvelOld]
  -- Continuation creates no bends: every retained bend is an earlier encounter.
  · intro u hu
    have hne : (r.ray.truncate L).bends u ≠ 0 := Finsupp.mem_support_iff.mp hu
    rw [FiniteAffineRay.bends_truncate_apply] at hne
    split_ifs at hne with hu₀
    · obtain ⟨j, hj⟩ := r.bends_recorded (u + L) (Finsupp.mem_support_iff.mpr hne)
      exact ⟨Fin.natAdd m j, by rw [hparamOld, ← hj]; ring⟩
    · exact (hne rfl).elim
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, hparamNew,
        FiniteAffineRay.truncate_apply _ _ (sub_nonpos.mpr (hlt j).le), sub_add_cancel]
      rw [hvalue (hpos j).le]
      exact hheight j
    · simp only [Fin.append_right, hparamOld,
        FiniteAffineRay.truncate_apply _ _
          (sub_nonpos.mpr ((hneg j).le.trans hL)), sub_add_cancel]
      exact r.height_eq j
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, hparamNew,
        FiniteAffineRay.truncate_apply _ _ (sub_nonpos.mpr (hlt j).le), sub_add_cancel]
      rw [hvalue (hpos j).le]
      exact hinc j
    · simp only [Fin.append_right, hparamOld,
        FiniteAffineRay.truncate_apply _ _
          (sub_nonpos.mpr ((hneg j).le.trans hL)), sub_add_cancel]
      exact r.incidence j
  -- Avoidance on the original half-line comes from `r`; on the added segment
  -- the complete new encounter list is removed from the wall-avoidance test.
  · intro a u hu hn
    rw [FiniteAffineRay.truncate_apply _ _ hu.le]
    rcases lt_trichotomy (u + L) 0 with hold | he | hnew
    · apply r.avoids_walls a _ hold
      intro j hj
      exact hn (Fin.natAdd m j) (by rw [hparamOld]; linarith)
    · rw [he, r.ray.eval_zero, r.endpoint_eq]
      exact r.off_walls a
    · rw [hvalue hnew.le]
      apply hW a _ hnew (by linarith)
      intro j hj
      exact hn (Fin.castAdd n j) (by rw [hparamNew]; linarith)
  · intro a u hu
    rw [FiniteAffineRay.truncate_apply _ _ hu]
    by_cases hold : u + L ≤ 0
    · exact r.avoids_singular a _ hold
    · rw [hvalue (le_of_not_ge hold)]
      exact hS a _ (lt_of_not_ge hold) (by linarith)
  · intro a
    by_cases hzero : L = 0
    · simpa only [hzero, zero_smul, sub_zero] using r.off_walls a
    · exact hW a L (lt_of_le_of_ne hL (Ne.symm hzero)) le_rfl
        (fun j he => (hlt j).ne he.symm)

/-- Continuation translates the endpoint of the complete original finite ray.
In particular its original half-line is recovered by shifting time by `L`. -/
@[simp]
theorem ray_continueStraight :
    (r.continueStraight L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).ray =
      r.ray.truncate L := (rfl)

/-- New encounter times translate by `L`; every earlier encounter has the same
translation, and the endpoint remains at time zero. -/
@[simp]
theorem parameter_continueStraight :
    (r.continueStraight L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).parameter =
      Fin.cons 0 (Fin.append (fun j => τ j - L) (fun j => r.parameter j.succ - L)) := (rfl)

end Mei.Convex.AdmissibleRayRealization
