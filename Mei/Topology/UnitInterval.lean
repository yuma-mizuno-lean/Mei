/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Interval meshes avoiding countable sets

An arbitrarily small positive mesh size can be chosen so that its multiples,
clamped to the unit interval, avoid any prescribed countable set missing the
endpoints. This permits subdivision vertices to avoid crossing parameters while
retaining the metric bounds of a uniform mesh.

A monotone mesh can moreover be refined to pass through finitely many prescribed
times, such as the breakpoints of a polygonal parametrization, with every new cell
inside an old one (`unitInterval.exists_monotone_refinement`).

The construction uses Mathlib's `Set.Countable.dense_compl` and the existing
`Set.Icc.addNSMul` mesh, including its eventual constancy and mesh-size bounds.
The refinement enumerates the union of the old vertices and the new times by
Mathlib's `Finset.orderEmbOfFin`.
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

namespace unitInterval

/-- A mesh of the unit interval starting at `0` and eventually equal to `1` can be refined to
a monotone mesh passing through finitely many prescribed times. Every vertex of the refinement
is an original vertex or a prescribed time. Every cell of the refinement lies between two
consecutive original vertices, so for a monotone original mesh it lies in an original cell. -/
theorem exists_monotone_refinement (t : ℕ → I) (ht0 : t 0 = 0) {m : ℕ}
    (htail : ∀ n, m ≤ n → t n = 1) (T : Finset I) :
    ∃ (m' : ℕ) (t' : ℕ → I), t' 0 = 0 ∧ Monotone t' ∧ (∀ n, m' ≤ n → t' n = 1) ∧
      (∀ n, (∃ a, t' n = t a) ∨ t' n ∈ T) ∧ (∀ τ ∈ T, ∃ a, t' a = τ) ∧
      ∀ a, ∃ c, t c ≤ t' a ∧ t' (a + 1) ≤ t (c + 1) := by
  classical
  -- Enumerate the old vertices together with the prescribed times in increasing order.
  let A : Finset I := (Finset.range (m + 1)).image t ∪ T
  have hmemA (a : ℕ) : t a ∈ A := by
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨min a m, by simp, ?_⟩)
    rcases le_total a m with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, htail a h, htail m le_rfl]
  have hk : 0 < A.card := Finset.card_pos.mpr ⟨_, hmemA 0⟩
  let g := A.orderEmbOfFin rfl
  let t' : ℕ → I := fun n => if h : n < A.card then g ⟨n, h⟩ else 1
  have hlt {n : ℕ} (h : n < A.card) : t' n = g ⟨n, h⟩ := by simp only [t', h, ↓reduceDIte]
  have hge {n : ℕ} (h : ¬n < A.card) : t' n = 1 := by simp only [t', h, ↓reduceDIte]
  have hfirst : t' 0 = 0 := by
    rw [hlt hk, A.orderEmbOfFin_zero rfl hk]
    exact le_antisymm (ht0 ▸ A.min'_le _ (hmemA 0)) (nonneg _)
  have hlast : t' (A.card - 1) = 1 := by
    rw [hlt (by omega), A.orderEmbOfFin_last rfl hk]
    exact le_antisymm (le_one _) (htail m le_rfl ▸ A.le_max' _ (hmemA m))
  have hmono' : Monotone t' := by
    intro a b hab
    by_cases hb : b < A.card
    · rw [hlt hb, hlt (lt_of_le_of_lt hab hb)]
      exact g.monotone (Fin.mk_le_mk.mpr hab)
    · rw [hge hb]
      exact le_one _
  have htail' (n : ℕ) (hn : A.card - 1 ≤ n) : t' n = 1 := by
    by_cases h : n < A.card
    · rw [show n = A.card - 1 by omega, hlast]
    · exact hge h
  have hmem' (n : ℕ) : t' n ∈ A := by
    by_cases h : n < A.card
    · rw [hlt h]
      exact A.orderEmbOfFin_mem rfl _
    · rw [hge h]
      exact htail m le_rfl ▸ hmemA m
  -- The next refined vertex is at most every larger element of the enumerated set.
  have hnext (a : ℕ) {x : I} (hx : x ∈ A) (hlt' : t' a < x) : t' (a + 1) ≤ x := by
    obtain ⟨j, rfl⟩ : x ∈ Set.range g := by rwa [A.range_orderEmbOfFin rfl]
    by_cases ha : a < A.card
    · rw [hlt ha] at hlt'
      have haj : a < j.val := Fin.lt_def.mp (g.lt_iff_lt.mp hlt')
      rw [hlt (show a + 1 < A.card by omega)]
      exact g.monotone (Fin.mk_le_mk.mpr haj)
    · rw [hge ha] at hlt'
      exact absurd hlt' (not_lt.mpr (le_one _))
  refine ⟨A.card - 1, t', hfirst, hmono', htail', fun n => ?_, fun τ hτ => ?_, fun a => ?_⟩
  · rcases Finset.mem_union.mp (hmem' n) with h | h
    · obtain ⟨c, -, hc⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨c, hc.symm⟩
    · exact Or.inr h
  · obtain ⟨j, hj⟩ : τ ∈ Set.range g := by
      rw [A.range_orderEmbOfFin rfl]
      exact Finset.mem_union_right _ hτ
    exact ⟨j.val, (hlt j.isLt).trans hj⟩
  · -- Use the last original vertex weakly below the refined vertex.
    let c := Nat.findGreatest (fun c => t c ≤ t' a) m
    have hc : t c ≤ t' a :=
      Nat.findGreatest_spec (P := fun c => t c ≤ t' a) (Nat.zero_le m) (ht0 ▸ nonneg _)
    refine ⟨c, hc, ?_⟩
    by_cases hcm : c < m
    · exact hnext a (hmemA (c + 1)) (not_le.mp
        (Nat.findGreatest_is_greatest (Nat.lt_succ_self c) (by omega)))
    · rw [htail (c + 1) (by omega)]
      exact le_one _

end unitInterval
