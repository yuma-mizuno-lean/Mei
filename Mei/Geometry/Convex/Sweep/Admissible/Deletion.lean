/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible

/-!
# Deleting unchanged-direction encounters

An encounter at which the direction does not change can be deleted from an
admissible ray when its encounter point misses the retained wall family. The
ray itself, its incoming tail and all remaining encounter parameters are
preserved. This applies when a wall becomes inactive after truncation or
coefficient specialization. A coincident retained wall must still be recorded:
the deleted point being off the retained walls is also a necessary condition.

`restrictEncounters` retains any ordered subrecord with the original times,
provided omitted encounters have zero bend and miss the retained walls. Both
single-encounter and varying-chamber deletion use this construction.

The construction uses `FiniteAffineRay.directionAt_sub_eq_bends` to show that
an unchanged-direction encounter is not a bend, and Mathlib's `Fin.removeNth`
to delete the encounter and merge the adjacent segments. Directions with zero
spatial value are allowed, and no rationality, genericity or finiteness of the
wall family is required. For the broken-line interpretation see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set

section Restriction

variable {V J J' K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n m : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Retain an ordered subset of the encounter record, with its original times.
Omitted encounters must have zero bend and miss every retained wall. The
parameter inclusion retains zero and the successors of retained arrow indices;
its selected directions must agree with those at the retained outgoing segments. -/
def restrictEncounters (r : AdmissibleRayRealization f c v P W S C Q)
    (t : Fin m → Fin n) (τ : Fin (m + 1) → Fin (n + 1))
    (hzero : τ 0 = 0) (hmono : StrictMono τ)
    (hsucc : ∀ j, τ j.succ = (t j).succ)
    (hdir : ∀ j, v (τ j.castSucc) = v (t j).castSucc)
    (W' : J' → Set V) (u : J' → J) (hW : ∀ a, W' a ⊆ W (u a))
    (hmiss : ∀ j, j ∉ range t → r.ray.bends (r.parameter j.succ) = 0 ∧
      ∀ a, r.ray (r.parameter j.succ) ∉ W' a) :
    AdmissibleRayRealization (f ∘ t) (c ∘ t) (v ∘ τ) (P ∘ t) W' S C Q where
  ray := r.ray
  parameter := r.parameter ∘ τ
  parameter_zero := by simp only [Function.comp_apply, hzero, r.parameter_zero]
  strictAnti_parameter := r.strictAnti_parameter.comp_strictMono hmono
  transverse j := by simpa only [Function.comp_apply, hdir] using r.transverse (t j)
  endpoint_eq := r.endpoint_eq
  directionAt_eq j := r.directionAt_eq (τ j)
  bends_recorded z hz := by
    obtain ⟨j, hj⟩ := r.bends_recorded z hz
    by_cases h : j ∈ range t
    · obtain ⟨i, rfl⟩ := h
      exact ⟨i, by simpa only [Function.comp_apply, hsucc] using hj⟩
    · exact ((Finsupp.mem_support_iff.mp hz) (hj ▸ (hmiss j h).1)).elim
  height_eq j := by simpa only [Function.comp_apply, hsucc] using r.height_eq (t j)
  incidence j := by simpa only [Function.comp_apply, hsucc] using r.incidence (t j)
  avoids_walls a z hz hne := by
    by_cases h : ∃ j, j ∉ range t ∧ z = r.parameter j.succ
    · obtain ⟨j, hj, rfl⟩ := h
      exact (hmiss j hj).2 a
    · apply fun hmem => r.avoids_walls (u a) z hz ?_ (hW a hmem)
      intro j heq
      by_cases hj : j ∈ range t
      · obtain ⟨i, rfl⟩ := hj
        exact hne i (by simpa only [Function.comp_apply, hsucc] using heq)
      · exact h ⟨j, hj, heq⟩
  incoming := r.incoming
  avoids_singular := r.avoids_singular
  off_walls a ha := r.off_walls (u a) (hW a ha)

/-- Restricting the encounter record preserves the whole ray and incoming tail. -/
@[simp]
theorem ray_restrictEncounters (r : AdmissibleRayRealization f c v P W S C Q)
    (t : Fin m → Fin n) (τ : Fin (m + 1) → Fin (n + 1))
    (hzero : τ 0 = 0) (hmono : StrictMono τ)
    (hsucc : ∀ j, τ j.succ = (t j).succ)
    (hdir : ∀ j, v (τ j.castSucc) = v (t j).castSucc)
    (W' : J' → Set V) (u : J' → J) (hW : ∀ a, W' a ⊆ W (u a))
    (hmiss : ∀ j, j ∉ range t → r.ray.bends (r.parameter j.succ) = 0 ∧
      ∀ a, r.ray (r.parameter j.succ) ∉ W' a) :
    (r.restrictEncounters t τ hzero hmono hsucc hdir W' u hW hmiss).ray = r.ray := (rfl)

/-- Every retained encounter has its original time. -/
@[simp]
theorem parameter_restrictEncounters (r : AdmissibleRayRealization f c v P W S C Q)
    (t : Fin m → Fin n) (τ : Fin (m + 1) → Fin (n + 1))
    (hzero : τ 0 = 0) (hmono : StrictMono τ)
    (hsucc : ∀ j, τ j.succ = (t j).succ)
    (hdir : ∀ j, v (τ j.castSucc) = v (t j).castSucc)
    (W' : J' → Set V) (u : J' → J) (hW : ∀ a, W' a ⊆ W (u a))
    (hmiss : ∀ j, j ∉ range t → r.ray.bends (r.parameter j.succ) = 0 ∧
      ∀ a, r.ray (r.parameter j.succ) ∉ W' a) (j : Fin (m + 1)) :
    (r.restrictEncounters t τ hzero hmono hsucc hdir W' u hW hmiss).parameter j =
      r.parameter (τ j) := (rfl)

end Restriction

variable {V J J' K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin (n + 1) → V →L[ℝ] ℝ} {c : Fin (n + 1) → ℝ}
  {v : Fin (n + 2) → V} {P : Fin (n + 1) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization f c v P W S C Q)

variable (i : Fin (n + 1)) (hi : v i.succ = v i.castSucc)
  (W' : J' → Set V) (e : J' → J) (hW : ∀ a, W' a ⊆ W (e a))

include hi in
private theorem directionAt_removeNth (j : Fin (n + 1)) :
    r.ray.directionAt (i.succ.removeNth r.parameter j) = i.castSucc.removeNth v j := by
  rw [Fin.removeNth, r.directionAt_eq, Fin.removeNth]
  rcases lt_trichotomy j.val i.val with h | h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa using h.le),
      Fin.succAbove_of_castSucc_lt _ _ (by simpa using h)]
  · have hj : j = i := Fin.ext h
    subst j
    simpa only [Fin.succAbove_succ_self, Fin.succAbove_castSucc_self] using hi.symm
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa using h),
      Fin.succAbove_of_le_castSucc _ _ (by simpa using h.le)]

/-- Delete an unchanged-direction encounter and restrict the wall family.
The omitted point must miss every retained wall. All singular-avoidance and
incoming-source conditions are inherited from the original ray. -/
def removeEncounter
    (hoff : ∀ a, r.ray (r.parameter i.succ) ∉ W' a) :
    AdmissibleRayRealization (i.removeNth f) (i.removeNth c)
      (i.castSucc.removeNth v) (i.removeNth P) W' S C Q := by
  have hdir (j : Fin (n + 1)) :
      v (i.succ.succAbove j) = i.castSucc.removeNth v j :=
    (r.directionAt_eq _).symm.trans (directionAt_removeNth r i hi j)
  have hout (j : Fin n) :
      v (i.succ.succAbove j.castSucc) = v (i.succAbove j).castSucc := by
    simpa only [Fin.removeNth, Fin.castSucc_succAbove_castSucc] using hdir j.castSucc
  let g := r.restrictEncounters i.succAbove i.succ.succAbove
    (Fin.succ_succAbove_zero i) (Fin.strictMono_succAbove i.succ)
    (fun j => Fin.succ_succAbove_succ i j) hout W' e hW (fun j hj => by
      have hji : j = i := by
        by_contra h
        obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
        exact hj ⟨k, hk⟩
      subst j
      exact ⟨by rw [r.bends_parameter, hi, sub_self], hoff⟩)
  exact g.congrVelocity (funext hdir)

/-- Deletion preserves the entire finite affine ray, including its incoming tail. -/
@[simp]
theorem ray_removeEncounter (hoff : ∀ a, r.ray (r.parameter i.succ) ∉ W' a) :
    (r.removeEncounter i hi W' e hW hoff).ray = r.ray := by
  simp only [removeEncounter, ray_congrVelocity, ray_restrictEncounters]

/-- The endpoint parameter remains zero, and every other retained parameter is
its original value after deleting the selected encounter. -/
@[simp]
theorem parameter_removeEncounter (hoff : ∀ a, r.ray (r.parameter i.succ) ∉ W' a)
    (j : Fin (n + 1)) :
    (r.removeEncounter i hi W' e hW hoff).parameter j =
      r.parameter (i.succ.succAbove j) := by
  simp only [removeEncounter, parameter_congrVelocity, parameter_restrictEncounters]

include hi e hW in
/-- Deletion with the prescribed unchanged path and retained parameters is
possible exactly when the omitted point misses the retained walls. This detects
coincident walls which cannot be removed from the encounter record. -/
theorem exists_removeEncounter_iff :
    (∃ s : AdmissibleRayRealization (i.removeNth f) (i.removeNth c)
        (i.castSucc.removeNth v) (i.removeNth P) W' S C Q,
      s.ray = r.ray ∧ s.parameter = i.succ.removeNth r.parameter) ↔
      ∀ a, r.ray (r.parameter i.succ) ∉ W' a := by
  constructor
  · rintro ⟨s, hr, hp⟩ a
    have ht : r.parameter i.succ < 0 := by
      simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos i)
    rw [← hr]
    apply s.avoids_walls a _ ht
    intro j h
    rw [hp, Fin.removeNth] at h
    exact Fin.ne_succAbove i.succ j.succ (r.strictAnti_parameter.injective h)
  · intro hoff
    exact ⟨r.removeEncounter i hi W' e hW hoff, ray_removeEncounter ..,
      funext fun j => parameter_removeEncounter r i hi W' e hW hoff j⟩

end Mei.Convex.AdmissibleRayRealization
