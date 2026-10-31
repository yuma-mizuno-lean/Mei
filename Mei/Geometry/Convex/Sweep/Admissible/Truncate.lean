/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Affine.FiniteRay.Truncate

/-!
# Cutting admissible rays between encounters

An admissible ray can be cut inside any of its open segments, including its
incoming half-line. The cut removes the encounters closer to the old endpoint
and retains the entire earlier itinerary. Every retained encounter has its old
position and translated parameter; wall avoidance, singular avoidance and source
admission persist. No convexity or rationality assumptions are needed.

The construction uses `FiniteAffineRay.truncate` and the recorded-encounter
axioms of `AdmissibleRayRealization`. It supplies the geometric incoming piece
when a broken line is cut before its last change of decoration, as in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter

namespace Mei.Convex.AdmissibleRayRealization

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {f : Fin (m + n) → V →L[ℝ] ℝ} {c : Fin (m + n) → ℝ}
  {v : Fin (m + n + 1) → V} {P : Fin (m + n) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization f c v P W S C Q) (t : ℝ)
  (hupper : t < r.parameter (Fin.natAdd m (0 : Fin (n + 1))))
  (hlower : ∀ j : Fin n, r.parameter (Fin.natAdd m j).succ < t)

include hupper in
private theorem cut_neg : t < 0 := by
  have he := r.strictAnti_parameter.antitone (Fin.zero_le (Fin.natAdd m (0 : Fin (n + 1))))
  rw [r.parameter_zero] at he
  exact hupper.trans_le he

include hupper hlower in
private theorem parameter_lt_cut_iff (a : Fin (m + n)) :
    r.parameter a.succ < t ↔ m ≤ a.val := by
  constructor
  · intro ha
    by_contra hm
    have hi : a.succ ≤ Fin.natAdd m (0 : Fin (n + 1)) := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_natAdd, Fin.val_zero, add_zero]
      omega
    exact (not_lt_of_ge (r.strictAnti_parameter.antitone hi)) (ha.trans hupper)
  · intro ha
    obtain ⟨j, he⟩ : a ∈ range (Fin.natAdd m : Fin n → Fin (m + n)) := by
      rwa [Fin.range_natAdd]
    simpa only [he] using hlower j

include hupper hlower in
private theorem cut_ne_parameter (a : Fin (m + n)) : t ≠ r.parameter a.succ := by
  by_cases ha : m ≤ a.val
  · exact ((r.parameter_lt_cut_iff t hupper hlower a).mpr ha).ne'
  · have hi : a.succ ≤ Fin.natAdd m (0 : Fin (n + 1)) := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_natAdd, Fin.val_zero, add_zero]
      omega
    exact (hupper.trans_le (r.strictAnti_parameter.antitone hi)).ne

include hupper hlower in
private theorem directionAt_cut : r.ray.directionAt t = v (Fin.natAdd m (0 : Fin (n + 1))) := by
  rw [← r.directionAt_eq (Fin.natAdd m (0 : Fin (n + 1))), FiniteAffineRay.directionAt_def,
    FiniteAffineRay.directionAt_def]
  congr 1
  apply Finsupp.sum_congr
  intro b hb
  obtain ⟨a, rfl⟩ := r.bends_recorded b hb
  by_cases ha : m ≤ a.val
  · have ht := (r.parameter_lt_cut_iff t hupper hlower a).mpr ha
    have hi : Fin.natAdd m (0 : Fin (n + 1)) < a.succ := by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_natAdd, Fin.val_zero, add_zero]
      omega
    simp only [ite_eq_right ht.not_ge, ite_eq_right (r.strictAnti_parameter hi).not_ge]
  · have hi : a.succ ≤ Fin.natAdd m (0 : Fin (n + 1)) := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_natAdd, Fin.val_zero, add_zero]
      omega
    have hp := r.strictAnti_parameter.antitone hi
    simp only [ite_eq_left hp, ite_eq_left (hupper.trans_le hp).le]

/-- Cut inside the segment after the first `m` backward encounters. The remaining
`n` encounters and the incoming tail are retained, with the new endpoint at time
`t`. The wall family is unchanged, so the cut lies away from every wall. -/
def truncate :
    AdmissibleRayRealization (fun j => f (Fin.natAdd m j))
      (fun j => c (Fin.natAdd m j)) (fun j : Fin (n + 1) => v (Fin.natAdd m j))
      (fun j => P (Fin.natAdd m j)) W S C (r.ray t) where
  -- Translate the retained encounters, using their original order and directions.
  ray := r.ray.truncate t
  parameter := Fin.cons 0 (fun j => r.parameter (Fin.natAdd m j).succ - t)
  parameter_zero := by simp
  strictAnti_parameter := by
    refine (Fin.strictMono_cons (α := ℝᵒᵈ)).mpr ⟨?_, ?_⟩
    · intro j
      exact sub_neg.mpr (hlower j)
    · intro a b hab
      exact sub_lt_sub_right
        (r.strictAnti_parameter (Fin.strictMono_succ (Fin.strictMono_natAdd m hab))) t
  transverse j := r.transverse (Fin.natAdd m j)
  endpoint_eq := FiniteAffineRay.endpoint_truncate _ _
  directionAt_eq := by
    intro j
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      rw [FiniteAffineRay.directionAt_truncate _ _ le_rfl, zero_add]
      exact r.directionAt_cut t hupper hlower
    | succ j =>
      simp only [Fin.cons_succ]
      rw [FiniteAffineRay.directionAt_truncate _ _ (sub_nonpos.mpr (hlower j).le),
        sub_add_cancel]
      exact r.directionAt_eq (Fin.natAdd m j).succ
  bends_recorded := by
    intro s hs
    have hsneg := (r.ray.truncate t).bend_neg s hs
    have hne := Finsupp.mem_support_iff.mp hs
    rw [FiniteAffineRay.bends_truncate_apply, ite_eq_left hsneg] at hne
    obtain ⟨a, ha⟩ := r.bends_recorded (s + t) (Finsupp.mem_support_iff.mpr hne)
    have ham : m ≤ a.val := (r.parameter_lt_cut_iff t hupper hlower a).mp
      (by rw [← ha]; linarith)
    obtain ⟨j, he⟩ : a ∈ range (Fin.natAdd m : Fin n → Fin (m + n)) := by
      rwa [Fin.range_natAdd]
    refine ⟨j, ?_⟩
    simp only [Fin.cons_succ, he]
    linarith
  height_eq := by
    intro j
    simp only [Fin.cons_succ]
    rw [FiniteAffineRay.truncate_apply _ _ (sub_nonpos.mpr (hlower j).le), sub_add_cancel]
    exact r.height_eq (Fin.natAdd m j)
  incidence := by
    intro j
    simp only [Fin.cons_succ]
    rw [FiniteAffineRay.truncate_apply _ _ (sub_nonpos.mpr (hlower j).le), sub_add_cancel]
    exact r.incidence (Fin.natAdd m j)
  -- Every old encounter before the cut belongs to the retained suffix.
  avoids_walls := by
    intro a s hs hrecord
    rw [FiniteAffineRay.truncate_apply _ _ hs.le]
    apply r.avoids_walls a (s + t) (by linarith [r.cut_neg t hupper])
    intro b hb
    have hbm : m ≤ b.val := (r.parameter_lt_cut_iff t hupper hlower b).mp
      (by rw [← hb]; linarith)
    obtain ⟨j, he⟩ : b ∈ range (Fin.natAdd m : Fin n → Fin (m + n)) := by
      rwa [Fin.range_natAdd]
    apply hrecord j
    simp only [Fin.cons_succ, he]
    linarith
  incoming := (r.ray.eventually_truncate_mem_iff t C).mpr r.incoming
  avoids_singular := by
    intro a s hs
    rw [FiniteAffineRay.truncate_apply _ _ hs]
    exact r.avoids_singular a (s + t) (by linarith [r.cut_neg t hupper])
  off_walls a := r.avoids_walls a t (r.cut_neg t hupper)
    (r.cut_ne_parameter t hupper hlower)

/-- The cut realization uses exactly the canonical truncated ray. -/
@[simp]
theorem ray_truncate : (r.truncate t hupper hlower).ray = r.ray.truncate t := (rfl)

/-- Retained encounter parameters are translated by the cut. -/
@[simp]
theorem parameter_truncate_succ (j : Fin n) :
    (r.truncate t hupper hlower).parameter j.succ =
      r.parameter (Fin.natAdd m j).succ - t := (rfl)

/-- Every point of the retained incoming path is unchanged, with translated time. -/
theorem truncate_ray_apply {s : ℝ} (hs : s ≤ 0) :
    (r.truncate t hupper hlower).ray s = r.ray (s + t) :=
  r.ray.truncate_apply t hs

/-- The retained encounter occurs at exactly its original geometric point. -/
theorem truncate_ray_parameter_succ (j : Fin n) :
    (r.truncate t hupper hlower).ray ((r.truncate t hupper hlower).parameter j.succ) =
      r.ray (r.parameter (Fin.natAdd m j).succ) := by
  rw [parameter_truncate_succ, truncate_ray_apply _ _ _ _ (sub_nonpos.mpr (hlower j).le),
    sub_add_cancel]

end Mei.Convex.AdmissibleRayRealization
