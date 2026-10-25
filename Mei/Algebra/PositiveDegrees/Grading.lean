/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Map
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Positive gradings and degree submodules

A positive grading is supported on the nonzero degrees of positive degree data.
For any internal module grading, the pieces above a cutoff span a homogeneous
submodule, characterized by vanishing of all components at or below the cutoff.
For a positive grading, the zero cutoff submodule is the whole module.

These submodules provide degree filtrations without requiring freeness or finite
rank of the homogeneous pieces.
-/

public section

namespace Mei

variable {N R M : Type*} [AddCommMonoid N]
  [Semiring R] [AddCommMonoid M] [Module R M]

/-- A grading is positive when its pieces vanish outside the nonzero allowed degrees. -/
class IsPositiveGrading (d : PositiveDegrees N) (ℒ : N → Submodule R M) : Prop where
  /-- The only possibly nonzero pieces have nonzero allowed degree. -/
  eq_bot : ∀ n, n ∉ d.monoid ∨ n = 0 → ℒ n = ⊥

namespace PositiveDegrees

variable (d : PositiveDegrees N) (ℒ : N → Submodule R M)

/-- The sum of the homogeneous pieces of degree strictly greater than `k`. -/
def degreeSubmodule (k : ℕ) : Submodule R M :=
  ⨆ n : {n : N // (k : ℤ) < d.degree n}, ℒ n

/-- The defining sum for the degree submodule. -/
theorem degreeSubmodule_def (k : ℕ) :
    d.degreeSubmodule ℒ k = ⨆ n : {n : N // (k : ℤ) < d.degree n}, ℒ n := (rfl)

/-- A homogeneous piece above the cutoff lies in the degree submodule. -/
theorem le_degreeSubmodule {n : N} {k : ℕ} (hn : (k : ℤ) < d.degree n) :
    ℒ n ≤ d.degreeSubmodule ℒ k :=
  le_iSup (fun n : {n : N // (k : ℤ) < d.degree n} => ℒ n) ⟨n, hn⟩

/-- Degree submodules decrease as the cutoff increases. -/
theorem degreeSubmodule_antitone : Antitone (d.degreeSubmodule ℒ) := by
  intro k l h
  rw [degreeSubmodule_def]
  refine iSup_le fun n => d.le_degreeSubmodule ℒ ?_
  have := n.property
  omega

/-- A homogeneous linear map carries degree submodules into degree submodules
at the cutoffs prescribed by its positive degree map. Only the source grading
needs positive support; no direct-sum decomposition is required. -/
theorem map_degreeSubmodule_le {N' M' : Type*} [AddCommMonoid N']
    [AddCommMonoid M'] [Module R M'] {e : PositiveDegrees N'}
    (T : PositiveDegreeMap d e) (ℒ' : N' → Submodule R M')
    [IsPositiveGrading d ℒ] (f : M →ₗ[R] M')
    (hf : ∀ n, ℒ n ≤ (ℒ' (T n)).comap f) (k : ℕ) :
    (d.degreeSubmodule ℒ (T.modulus k)).map f ≤ e.degreeSubmodule ℒ' k := by
  rw [degreeSubmodule_def, Submodule.map_iSup]
  refine iSup_le fun n => ?_
  by_cases hn : n.val ∈ d.monoid
  · exact (Submodule.map_le_iff_le_comap.mpr (hf n.val)).trans
      (e.le_degreeSubmodule ℒ' (T.degree_gt k hn n.property))
  · rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n.val (Or.inl hn),
      Submodule.map_bot]
    exact bot_le

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

/-- Membership means that all components at or below the cutoff vanish. -/
theorem mem_degreeSubmodule_iff {x : M} {k : ℕ} :
    x ∈ d.degreeSubmodule ℒ k ↔
      ∀ n, d.degree n ≤ k → (DirectSum.decompose ℒ x n : M) = 0 := by
  constructor
  · intro hx n hn
    rw [degreeSubmodule_def] at hx
    refine Submodule.iSup_induction _ (motive := fun x =>
      (DirectSum.decompose ℒ x n : M) = 0) hx
      (fun m x hx => ?_) ?_ (fun x y hx hy => ?_)
    · exact DirectSum.decompose_of_mem_ne ℒ hx (by
        intro h
        have := m.property
        rw [h] at this
        omega)
    · simp
    · simp [hx, hy]
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose ℒ x]
    apply Submodule.sum_mem
    intro n _
    by_cases hn : (k : ℤ) < d.degree n
    · exact d.le_degreeSubmodule ℒ hn (DirectSum.decompose ℒ x n).property
    · rw [hx n (le_of_not_gt hn)]
      exact Submodule.zero_mem _

/-- A homogeneous element is above the cutoff exactly when it is zero or its degree is above it. -/
theorem mem_degreeSubmodule_of_mem_iff {n : N} {x : M} {k : ℕ} (hx : x ∈ ℒ n) :
    x ∈ d.degreeSubmodule ℒ k ↔ x = 0 ∨ (k : ℤ) < d.degree n := by
  constructor
  · intro h
    by_cases hn : (k : ℤ) < d.degree n
    · exact Or.inr hn
    · exact Or.inl (by
        simpa only [DirectSum.decompose_of_mem_same ℒ hx] using
          (d.mem_degreeSubmodule_iff ℒ).mp h n (le_of_not_gt hn))
  · rintro (rfl | hn)
    · exact Submodule.zero_mem _
    · exact d.le_degreeSubmodule ℒ hn hx

/-- Every degree submodule is closed under taking homogeneous components. -/
theorem degreeSubmodule_isHomogeneous (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous ℒ (d.degreeSubmodule ℒ k) := by
  intro n x hx
  by_cases hn : (k : ℤ) < d.degree n
  · exact d.le_degreeSubmodule ℒ hn (DirectSum.decompose ℒ x n).property
  · rw [(d.mem_degreeSubmodule_iff ℒ).mp hx n (le_of_not_gt hn)]
    exact Submodule.zero_mem _

variable [IsPositiveGrading d ℒ]

omit [DecidableEq N] [DirectSum.Decomposition ℒ] in
/-- Any nonzero homogeneous element has strictly positive degree. -/
theorem degree_pos_of_mem_ne_zero {n : N} {x : M} (hx : x ∈ ℒ n) (hne : x ≠ 0) :
    0 < d.degree n := by
  have hn : n ∈ d.monoid ∧ n ≠ 0 := by
    by_contra h
    have hb := IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (by tauto)
    exact hne (by simpa [hb] using hx)
  exact d.degree_pos hn.1 hn.2

/-- All of a positively graded module lies above the zero cutoff. -/
@[simp]
theorem degreeSubmodule_zero : d.degreeSubmodule ℒ 0 = ⊤ := by
  apply top_unique
  rw [← (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top]
  refine iSup_le fun n x hx => ?_
  by_cases h : x = 0
  · simp [h]
  · exact d.le_degreeSubmodule ℒ (d.degree_pos_of_mem_ne_zero ℒ hx h) hx

end PositiveDegrees
end Mei
