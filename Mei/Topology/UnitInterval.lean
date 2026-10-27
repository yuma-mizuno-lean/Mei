/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Interval meshes avoiding countable sets

An arbitrarily small positive mesh size can be chosen so that its multiples,
clamped to the unit interval, avoid any prescribed countable set missing the
endpoints. This permits subdivision vertices to avoid crossing parameters while
retaining the metric bounds of a uniform mesh.

The construction uses Mathlib's `Set.Countable.dense_compl` and the existing
`Set.Icc.addNSMul` mesh, including its eventual constancy and mesh-size bounds.
-/

public section

open Set

namespace Set.Countable

/-- Choose an arbitrarily small uniform mesh whose clamped vertices miss a
countable exceptional set. The endpoints must already avoid that set. -/
theorem exists_pos_addNSMul_notMem {S : Set ℝ} (hS : S.Countable)
    (h0 : 0 ∉ S) (h1 : 1 ∉ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Ioo (0 : ℝ) ε, ∀ n : ℕ,
      (Icc.addNSMul (zero_le_one : (0 : ℝ) ≤ 1) δ n : ℝ) ∉ S := by
  let B := ⋃ n : ℕ, (fun s : ℝ => s / n) '' S
  have hB : B.Countable := countable_iUnion fun n => hS.image (fun s => s / n)
  obtain ⟨δ, hδ, hδB⟩ := (hB.dense_compl ℝ).inter_open_nonempty
    (Ioo (0 : ℝ) ε) isOpen_Ioo (nonempty_Ioo.mpr hε)
  refine ⟨δ, hδ, fun n hn => ?_⟩
  have hnonneg : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ.1.le
  have he : (Icc.addNSMul (zero_le_one : (0 : ℝ) ≤ 1) δ n : ℝ) =
      min 1 ((n : ℝ) * δ) := by
    simp [Icc.addNSMul, coe_projIcc, nsmul_eq_mul, le_min zero_le_one hnonneg]
  rw [he] at hn
  by_cases htop : 1 ≤ (n : ℝ) * δ
  · exact h1 (by simpa only [min_eq_left htop] using hn)
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact h0 (by simpa using hn)
    apply hδB
    refine mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨(n : ℝ) * δ, by simpa only [min_eq_right (le_of_not_ge htop)] using hn, ?_⟩
    exact mul_div_cancel_left₀ δ (Nat.cast_ne_zero.mpr hn0)

end Set.Countable
