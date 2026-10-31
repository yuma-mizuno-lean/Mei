/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
import Mathlib.Data.List.Sort

/-!
# Recovering encounter times from an admissible path

When every recorded encounter belongs to the obstacle family, the path determines
its entire ordered list of encounter times. Avoidance away from recorded times
gives exhaustion, and strict ordering removes any ambiguity in enumeration.
The two itineraries may have different lengths and different local data.
Agreement on a closed terminal interval determines just the corresponding
terminal encounter lists, without constraining either earlier path.

This uses the incidence and avoidance axioms of `AdmissibleRayRealization` and
Mathlib's `List.Pairwise.eq_of_mem_iff`. It is useful when identifying straight
incoming contributions to decorated-ray sums.
-/

public noncomputable section

open Set

namespace Mei.Convex.AdmissibleRayRealization

variable {V J K K' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n m : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {f' : Fin m → V →L[ℝ] ℝ} {c' : Fin m → ℝ}
  {v' : Fin (m + 1) → V} {P' : Fin m → Set V}
  {W : J → Set V} {S : K → Set V} {S' : K' → Set V} {C C' : Set V} {Q : V}

/-- A recorded encounter lying on an obstacle occurs among the encounter times
of any admissible realization of the same path. -/
theorem exists_parameter_eq_of_ray_eq
    (r : AdmissibleRayRealization f c v P W S C Q)
    (s : AdmissibleRayRealization f' c' v' P' W S' C' Q)
    (hr : ∀ t ≤ 0, r.ray t = s.ray t)
    (j : Fin n) (hP : P j ⊆ ⋃ a, W a) :
    ∃ i : Fin m, r.parameter j.succ = s.parameter i.succ := by
  classical
  have ht : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hP (r.incidence j))
  rw [hr _ ht.le] at ha
  by_contra hn
  exact s.avoids_walls a _ ht (by simpa using hn) ha

/-- Two admissible realizations of the same negative half-line have the same
ordered encounter times, provided every recorded encounter lies on an obstacle.
Identity encounters remain in the list. -/
theorem encounterParameters_eq_of_ray_eq
    (r : AdmissibleRayRealization f c v P W S C Q)
    (s : AdmissibleRayRealization f' c' v' P' W S' C' Q)
    (hr : ∀ t ≤ 0, r.ray t = s.ray t)
    (hP : ∀ j, P j ⊆ ⋃ a, W a) (hP' : ∀ j, P' j ⊆ ⋃ a, W a) :
    List.ofFn (fun j : Fin n => r.parameter j.succ) =
      List.ofFn (fun j : Fin m => s.parameter j.succ) := by
  have hs (r : AdmissibleRayRealization f c v P W S C Q) :
      (List.ofFn fun j : Fin n => r.parameter j.succ).Pairwise (· > ·) :=
    List.pairwise_ofFn.mpr fun i j hij =>
      r.strictAnti_parameter (Fin.strictMono_succ hij)
  have hs' : (List.ofFn fun j : Fin m => s.parameter j.succ).Pairwise (· > ·) :=
    List.pairwise_ofFn.mpr fun i j hij =>
      s.strictAnti_parameter (Fin.strictMono_succ hij)
  apply (hs r).eq_of_mem_iff hs'
  intro t
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := r.exists_parameter_eq_of_ray_eq s hr j (hP j)
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := s.exists_parameter_eq_of_ray_eq r (fun t ht => (hr t ht).symm) i (hP' i)
    exact ⟨j, hj.symm⟩

/-- Every encounter on a common closed terminal path piece appears in the
other ray's terminal encounter list. The earlier paths need not agree. -/
theorem encounterParameters_take_subset_of_ray_eqOn
    (r : AdmissibleRayRealization f c v P W S C Q)
    (s : AdmissibleRayRealization f' c' v' P' W S' C' Q)
    (j : Fin n) (l : Fin m) (ht : r.parameter j.succ = s.parameter l.succ)
    (hr : ∀ t ∈ Icc (r.parameter j.succ) 0, r.ray t = s.ray t)
    (hP : ∀ i ≤ j, P i ⊆ ⋃ a, W a) :
    (List.ofFn (fun i : Fin n => r.parameter i.succ)).take (j.val + 1) ⊆
      (List.ofFn (fun i : Fin m => s.parameter i.succ)).take (l.val + 1) := by
  intro t hmem
  obtain ⟨i, hi, he⟩ := List.mem_take_iff_getElem.mp hmem
  have hin : i < n := by simpa only [List.length_ofFn] using (lt_min_iff.mp hi).2
  let a : Fin n := ⟨i, hin⟩
  have ha : a ≤ j := by
    have := (lt_min_iff.mp hi).1
    simpa only [a, Fin.le_def] using (Nat.le_of_lt_succ this)
  have he' : r.parameter a.succ = t := by simpa only [List.getElem_ofFn] using he
  have hneg : r.parameter a.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos a)
  have hlow := r.strictAnti_parameter.antitone (Fin.succ_le_succ_iff.mpr ha)
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hP a ha (r.incidence a))
  rw [hr _ ⟨hlow, hneg.le⟩] at hb
  have hex : ∃ b : Fin m, r.parameter a.succ = s.parameter b.succ := by
    by_contra hn
    exact s.avoids_walls b _ hneg (by simpa using hn) hb
  obtain ⟨b, hb⟩ := hex
  have hbl : b ≤ l := by
    have hh : s.parameter l.succ ≤ s.parameter b.succ := by rwa [← ht, ← hb]
    exact Fin.succ_le_succ_iff.mp (s.strictAnti_parameter.le_iff_ge.mp hh)
  apply List.mem_take_iff_getElem.mpr
  refine ⟨b.val, ?_, ?_⟩
  · simp only [List.length_ofFn, lt_min_iff]
    exact ⟨Nat.lt_succ_of_le (Fin.le_def.mp hbl), b.isLt⟩
  · simpa only [List.getElem_ofFn] using hb.symm.trans he'

/-- The closed terminal piece of a path determines all its ordered encounter
times, including its initial encounter. Earlier pieces may differ completely.
Every terminal encounter on either ray must belong to the obstacle family. -/
theorem encounterParameters_take_eq_of_ray_eqOn
    (r : AdmissibleRayRealization f c v P W S C Q)
    (s : AdmissibleRayRealization f' c' v' P' W S' C' Q)
    (j : Fin n) (l : Fin m) (ht : r.parameter j.succ = s.parameter l.succ)
    (hr : ∀ t ∈ Icc (r.parameter j.succ) 0, r.ray t = s.ray t)
    (hP : ∀ i ≤ j, P i ⊆ ⋃ a, W a) (hP' : ∀ i ≤ l, P' i ⊆ ⋃ a, W a) :
    (List.ofFn (fun i : Fin n => r.parameter i.succ)).take (j.val + 1) =
      (List.ofFn (fun i : Fin m => s.parameter i.succ)).take (l.val + 1) := by
  have hp : (List.ofFn (fun i : Fin n => r.parameter i.succ)).Pairwise (· > ·) :=
    List.pairwise_ofFn.mpr fun i i' hii' =>
      r.strictAnti_parameter (Fin.strictMono_succ hii')
  have hp' : (List.ofFn (fun i : Fin m => s.parameter i.succ)).Pairwise (· > ·) :=
    List.pairwise_ofFn.mpr fun i i' hii' =>
      s.strictAnti_parameter (Fin.strictMono_succ hii')
  exact hp.take.eq_of_mem_iff hp'.take fun t =>
    ⟨fun h => r.encounterParameters_take_subset_of_ray_eqOn s j l ht hr hP h,
      fun h => s.encounterParameters_take_subset_of_ray_eqOn r l j ht.symm
        (fun t h => (hr t (by simpa only [ht] using h)).symm) hP' h⟩

end Mei.Convex.AdmissibleRayRealization
