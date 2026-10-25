/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Elimination of one nonnegative real variable

A finite system `a i * t ≤ b i` with `0 ≤ t` is feasible exactly when its
nonnegative rows are compatible with zero and each negative row is compatible
with every positive row. The compatibility conditions contain no divisions.

The witness is the maximum of zero and all lower bounds from the negative rows.
In particular the result handles empty systems and systems without upper or
lower bounds. This is the scalar elimination step for rational polyhedra;
the coefficients `a` and `b` in this file may be arbitrary real numbers.
-/

public section

namespace Mei

private theorem div_le_div_iff_of_neg_pos {a b c d : ℝ} (ha : a < 0) (hc : 0 < c) :
    b / a ≤ d / c ↔ a * d ≤ c * b := by
  rw [div_le_iff_of_neg ha, div_mul_eq_mul_div, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith

/-- Eliminate one nonnegative variable from finitely many scalar inequalities.
The right side uses only multiplication, addition, and order, so rational input
coefficients lead to rational compatibility inequalities. -/
theorem exists_nonneg_mul_le_iff {ι : Type*} [Finite ι] {a b : ι → ℝ} :
    (∃ t : ℝ, 0 ≤ t ∧ ∀ i, a i * t ≤ b i) ↔
      (∀ i, 0 ≤ a i → 0 ≤ b i) ∧
      (∀ i j, a i < 0 → 0 < a j → a i * b j ≤ a j * b i) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨fun i hi => (mul_nonneg hi ht).trans (h i), ?_⟩
    intro i j hi hj
    have h₁ := mul_le_mul_of_nonneg_left (h i) hj.le
    have h₂ := mul_le_mul_of_nonpos_left (h j) hi.le
    nlinarith
  · rintro ⟨hzero, hpair⟩
    let s : Finset ℝ := insert 0 ((Finset.univ.filter (fun i => a i < 0)).image
      (fun i => b i / a i))
    have hs : (0 : ℝ) ∈ s := Finset.mem_insert_self _ _
    let t := s.max' ⟨0, hs⟩
    refine ⟨t, s.le_max' 0 hs, ?_⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hmem : b i / a i ∈ s := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      exact (div_le_iff_of_neg' hi).mp (s.le_max' _ hmem)
    · simpa [hi] using hzero i hi.ge
    · rw [mul_comm (a i)]
      apply (le_div_iff₀ hi).mp
      change s.max' ⟨0, hs⟩ ≤ b i / a i
      apply s.max'_le
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact div_nonneg (hzero i hi.le) hi.le
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        have hjneg : a j < 0 := (Finset.mem_filter.mp hj).2
        exact (div_le_div_iff_of_neg_pos hjneg hi).mpr (hpair j i hjneg hi)

end Mei
