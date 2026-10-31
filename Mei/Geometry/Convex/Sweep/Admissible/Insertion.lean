/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Data.Fin.Insertion
public import Mathlib.Order.Fin.Tuple

/-!
# Reinserting transverse encounters in admissible rays

An encounter may be recorded inside an existing straight segment without changing
the ray. The segment direction is duplicated, all older encounter parameters are
retained, and the added wall joins the obstacle family. Admission of the incoming
tail and avoidance of singular sets are inherited from the original path.

The construction uses `AdmissibleRayRealization` and Mathlib's `Fin.insertNth`.
It is the geometric operation needed when an identity wall is restored to an
encounter itinerary; an unchanged spatial direction alone does not prescribe a
coefficient propagation map.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization f c v P W S C Q)
  (i : Fin (n + 1)) (t : ℝ)
  (hbefore : t < r.parameter i)
  (hafter : ∀ j, i < j → r.parameter j < t)

include hbefore hafter

/-- In the open segment immediately before a recorded parameter, the incoming
ray direction is the prescribed segment direction. This includes the infinite tail. -/
theorem directionAt_eq_between : r.ray.directionAt t = v i := by
  rw [← r.directionAt_eq i]
  simp only [FiniteAffineRay.directionAt_def]
  congr 1
  apply Finsupp.sum_congr
  intro b hb
  obtain ⟨j, rfl⟩ := r.bends_recorded b hb
  by_cases hj : j.succ ≤ i
  · have hp := r.strictAnti_parameter.antitone hj
    simp [hp, hbefore.le.trans hp]
  · have hp := hafter j.succ (lt_of_not_ge hj)
    have hq := r.strictAnti_parameter (lt_of_not_ge hj)
    simp [hp.not_ge, hq.not_ge]

/-- Insert a transverse encounter in a straight segment, retaining the actual
ray and every previous parameter. The added wall must have no unrecorded hit;
it may also meet the path at already recorded encounters. -/
def insertEncounter (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
    (htrans : m (v i) ≠ 0) (hheight : m (r.ray t) = b) (hinc : r.ray t ∈ H)
    (havoid : ∀ s, s < 0 → s ≠ t →
      (∀ j : Fin n, s ≠ r.parameter j.succ) → r.ray s ∉ H)
    (hoff : Q ∉ H) :
    AdmissibleRayRealization
      (i.insertNth (α := fun _ => V →L[ℝ] ℝ) m f)
      (i.insertNth (α := fun _ => ℝ) b c)
      (i.succ.insertNth (α := fun _ => V) (v i) v)
      (i.insertNth (α := fun _ => Set V) H P)
      (Sum.elim W (fun _ : Unit => H)) S C Q := by
  -- Embed the old encounter indices into the enlarged parameter tuple.
  let τ := i.succ.insertNth (α := fun _ => ℝ) t r.parameter
  have hτ (j : Fin n) : τ (i.succAbove j).succ = r.parameter j.succ := by
    simp [τ, ← Fin.succ_succAbove_succ]
  refine {
    ray := r.ray
    parameter := τ
    parameter_zero := ?_
    strictAnti_parameter := by
      apply (Fin.strictMono_insertNth_iff (α := ℝᵒᵈ) i.succ t r.parameter).mpr
      refine ⟨r.strictAnti_parameter, ?_, ?_⟩
      · intro j hj
        have hji : j ≤ i := by
          simpa only [Fin.castSucc_lt_iff_succ_le, Fin.succ_le_succ_iff] using hj
        exact hbefore.trans_le (r.strictAnti_parameter.antitone hji)
      · intro j hj
        apply hafter j
        simpa only [Fin.succ_le_castSucc_iff] using hj
    transverse := ?_
    endpoint_eq := r.endpoint_eq
    directionAt_eq := ?_
    bends_recorded := ?_
    height_eq := ?_
    incidence := ?_
    avoids_walls := ?_
    incoming := r.incoming
    avoids_singular := r.avoids_singular
    off_walls := ?_ }
  · calc
      τ 0 = τ (i.succ.succAbove 0) := by simp
      _ = r.parameter 0 := Fin.insertNth_apply_succAbove _ _ _ _
      _ = 0 := r.parameter_zero
  -- Check the inserted encounter and retained encounters separately.
  · intro j
    rw [Fin.insertNth_succ_castSucc]
    cases j using Fin.succAboveCases i <;> simp [r.transverse, htrans]
  · intro j
    cases j using Fin.succAboveCases i.succ
    · simpa [τ] using r.directionAt_eq_between i t hbefore hafter
    · simp [τ, r.directionAt_eq]
  · intro s hs
    obtain ⟨j, hj⟩ := r.bends_recorded s hs
    exact ⟨i.succAbove j, (hτ j).symm ▸ hj⟩
  · intro j
    cases j using Fin.succAboveCases i
    · simpa [τ] using hheight
    · simpa only [Fin.insertNth_apply_succAbove, hτ] using r.height_eq _
  · intro j
    cases j using Fin.succAboveCases i
    · simpa [τ] using hinc
    · simpa only [Fin.insertNth_apply_succAbove, hτ] using r.incidence _
  · intro a s hs hne
    have hold (j : Fin n) : s ≠ r.parameter j.succ := by
      simpa only [hτ] using hne (i.succAbove j)
    cases a with
    | inl a => exact r.avoids_walls a s hs hold
    | inr a => exact havoid s hs (by simpa [τ] using hne i) hold
  · intro a
    cases a with
    | inl a => exact r.off_walls a
    | inr a => exact hoff

variable (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
  (htrans : m (v i) ≠ 0) (hheight : m (r.ray t) = b) (hinc : r.ray t ∈ H)
  (havoid : ∀ s, s < 0 → s ≠ t →
    (∀ j : Fin n, s ≠ r.parameter j.succ) → r.ray s ∉ H)
  (hoff : Q ∉ H)

local notation "A" => AdmissibleRayRealization
  (i.insertNth (α := fun _ => V →L[ℝ] ℝ) m f)
  (i.insertNth (α := fun _ => ℝ) b c)
  (i.succ.insertNth (α := fun _ => V) (v i) v)
  (i.insertNth (α := fun _ => Set V) H P)
  (Sum.elim W (fun _ : Unit => H)) S C Q

/-- Reinsertion preserves the entire geometric ray, including its incoming tail. -/
@[simp]
theorem ray_insertEncounter :
    (r.insertEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).ray =
      r.ray := (rfl)

/-- The enlarged tuple contains the original parameters in order and the new time. -/
@[simp]
theorem parameter_insertEncounter :
    (r.insertEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).parameter =
      i.succ.insertNth (α := fun _ => ℝ) t r.parameter := (rfl)

/-- Each retained encounter keeps its original time. -/
@[simp]
theorem parameter_insertEncounter_succAbove (j : Fin n) :
    (r.insertEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).parameter
      (i.succAbove j).succ = r.parameter j.succ := by
  rw [parameter_insertEncounter, ← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove]

omit htrans hheight hinc havoid hoff in
/-- The geometric conditions for recording one extra encounter are necessary and
sufficient. All negative-time hits on the added wall must already be recorded or
occur at the inserted time; the endpoint must remain allowed. -/
theorem exists_insertEncounter_iff :
    (∃ s : A, s.ray = r.ray ∧
      s.parameter = i.succ.insertNth (α := fun _ => ℝ) t r.parameter) ↔
      m (v i) ≠ 0 ∧ m (r.ray t) = b ∧ r.ray t ∈ H ∧
        (∀ s, s < 0 → s ≠ t →
          (∀ j : Fin n, s ≠ r.parameter j.succ) → r.ray s ∉ H) ∧ Q ∉ H := by
  constructor
  · rintro ⟨s, hr, hp⟩
    have ht : s.parameter i.succ = t := by simp [hp]
    refine ⟨?_, ?_, ?_, ?_, s.off_walls (.inr ())⟩
    · simpa only [Fin.insertNth_apply_same, Fin.insertNth_succ_castSucc]
        using s.transverse i
    · simpa only [Fin.insertNth_apply_same, ht, hr] using s.height_eq i
    · simpa only [Fin.insertNth_apply_same, ht, hr] using s.incidence i
    · intro u hu hut huold
      rw [← hr]
      apply s.avoids_walls (.inr ()) u hu
      intro j
      cases j using Fin.succAboveCases i
      · simpa only [ht] using hut
      · simpa only [hp, ← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove]
          using huold _
  · rintro ⟨htrans, hheight, hinc, havoid, hoff⟩
    exact ⟨r.insertEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff,
      ray_insertEncounter .., parameter_insertEncounter ..⟩

end Mei.Convex.AdmissibleRayRealization
