/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Interval partitions avoiding countably many parameters

An open cover of the unit interval admits a finite monotone partition whose
vertices avoid any prescribed countable set, provided the endpoints avoid it.
This permits local segment identities to be summed without inserting vertices
at intersections being counted.

This extends Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval`. The central inputs are
its partition `Set.Icc.addNSMul` and `Set.Countable.dense_compl`.
-/

public section

open Set

namespace Mei

/-- Refine an open cover of the unit interval by a finite monotone partition
whose vertices avoid a prescribed countable set of real parameters. The sequence
is eventually the right endpoint, so repeated terminal vertices are allowed. -/
theorem exists_monotone_Icc_subset_open_cover_unitInterval_notMem
    {ι : Type*} {c : ι → Set unitInterval}
    (hc : ∀ j, IsOpen (c j)) (hcover : univ ⊆ ⋃ j, c j)
    {S : Set ℝ} (hS : S.Countable) (hzero : 0 ∉ S) (hone : 1 ∉ S) :
    ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∃ m, ∀ n ≥ m, t n = 1) ∧
      (∀ n, (t n : ℝ) ∉ S) ∧ ∀ n, ∃ j, Icc (t n) (t (n + 1)) ⊆ c j := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  -- Avoiding all quotients s / n keeps the mesh vertices away from S.
  let B : Set ℝ := ⋃ n : ℕ, (fun s : ℝ => s / n) '' S
  have hB : B.Countable := countable_iUnion fun _ => hS.image _
  obtain ⟨ε, hεB, hε⟩ := (hB.dense_compl ℝ).exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr hδ)
  let t := Icc.addNSMul (a := (0 : ℝ)) (b := 1) zero_le_one ε
  obtain ⟨m, hm⟩ := Icc.addNSMul_eq_right (a := (0 : ℝ)) (b := 1) zero_le_one hε.1
  refine ⟨t, Subtype.ext (Icc.addNSMul_zero _), Icc.monotone_addNSMul _ hε.1.le,
    ⟨m, fun n hn => Subtype.ext (hm n hn)⟩, ?_, ?_⟩
  · intro n hn
    have he : (t n : ℝ) = min 1 ((n : ℝ) * ε) := by
      simp [t, Icc.addNSMul, coe_projIcc, nsmul_eq_mul,
        mul_nonneg (Nat.cast_nonneg n) hε.1.le]
    rw [he] at hn
    by_cases hmin : 1 ≤ (n : ℝ) * ε
    · exact hone (by simpa only [min_eq_left hmin] using hn)
    · have hnS : (n : ℝ) * ε ∈ S := by
        simpa only [min_eq_right (le_of_not_ge hmin)] using hn
      by_cases hn0 : n = 0
      · subst n
        exact hzero (by simpa using hnS)
      · apply hεB
        exact mem_iUnion.mpr ⟨n,
          ⟨(n : ℝ) * ε, hnS, by simp [hn0]⟩⟩
  · intro n
    obtain ⟨j, hj⟩ := hball (t n) trivial
    refine ⟨j, fun u hu => hj ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    exact (Icc.abs_sub_addNSMul_le _ hε.1.le n hu).trans_lt hε.2

end Mei
