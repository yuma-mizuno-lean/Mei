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

end Mei.Convex.AdmissibleRayRealization
