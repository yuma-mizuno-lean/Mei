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
      (i.castSucc.removeNth v) (i.removeNth P) W' S C Q where
  ray := r.ray
  parameter := i.succ.removeNth r.parameter
  parameter_zero := by simpa only [Fin.removeNth, Fin.succ_succAbove_zero] using r.parameter_zero
  strictAnti_parameter := r.strictAnti_parameter.comp_strictMono (Fin.strictMono_succAbove i.succ)
  transverse j := by
    simpa only [Fin.removeNth, Fin.castSucc_succAbove_castSucc] using r.transverse (i.succAbove j)
  endpoint_eq := r.endpoint_eq
  directionAt_eq := directionAt_removeNth r i hi
  bends_recorded t ht := by
    obtain ⟨a, ha⟩ := r.bends_recorded t ht
    have hai : a ≠ i := by
      rintro rfl
      have hz : r.ray.bends t = 0 := by rw [ha, r.bends_parameter, hi, sub_self]
      exact (Finsupp.mem_support_iff.mp ht) hz
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hai
    exact ⟨j, by simpa only [Fin.removeNth, Fin.succ_succAbove_succ] using ha⟩
  height_eq j := by
    simpa only [Fin.removeNth, Fin.succ_succAbove_succ] using r.height_eq (i.succAbove j)
  incidence j := by
    simpa only [Fin.removeNth, Fin.succ_succAbove_succ] using r.incidence (i.succAbove j)
  avoids_walls a t ht hne := by
    by_cases hti : t = r.parameter i.succ
    · exact hti ▸ hoff a
    · apply fun h => r.avoids_walls (e a) t ht ?_ (hW a h)
      intro j
      by_cases hji : j = i
      · simpa only [hji] using hti
      · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hji
        simpa only [Fin.removeNth, Fin.succ_succAbove_succ] using hne b
  incoming := r.incoming
  avoids_singular := r.avoids_singular
  off_walls a h := r.off_walls (e a) (hW a h)

/-- Deletion preserves the entire finite affine ray, including its incoming tail. -/
@[simp]
theorem ray_removeEncounter (hoff : ∀ a, r.ray (r.parameter i.succ) ∉ W' a) :
    (r.removeEncounter i hi W' e hW hoff).ray = r.ray := (rfl)

/-- The endpoint parameter remains zero, and every other retained parameter is
its original value after deleting the selected encounter. -/
@[simp]
theorem parameter_removeEncounter (hoff : ∀ a, r.ray (r.parameter i.succ) ∉ W' a)
    (j : Fin (n + 1)) :
    (r.removeEncounter i hi W' e hW hoff).parameter j =
      r.parameter (i.succ.succAbove j) := (rfl)

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
    exact ⟨r.removeEncounter i hi W' e hW hoff, rfl, rfl⟩

end Mei.Convex.AdmissibleRayRealization
