/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Basic

/-!
# Positive multiples and relative degree cutoffs

These estimates locate terms and their predecessors in finite degree cutoffs.
-/

public section

open TauCeti (PositiveDegrees)

namespace TauCeti.PositiveDegrees

variable {N : Type*} [AddCommMonoid N] (d : PositiveDegrees N)

/-- The degree of the `(j + 1)`st multiple of a nonzero allowed degree exceeds `j`. -/
theorem lt_degree_succ_nsmul {n : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (j : ℕ) :
    (j : ℤ) < d.degree ((j + 1) • n) := by
  have h := d.degree_pos hn hn0
  rw [map_nsmul, nsmul_eq_mul]
  push_cast
  exact lt_of_lt_of_le (by omega : (j : ℤ) < j + 1)
    (le_mul_of_one_le_right (by omega) (by omega))

/-- Positive multiples of a nonzero allowed degree are nonzero. -/
theorem succ_nsmul_ne_zero {n : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (j : ℕ) :
    (j + 1) • n ≠ 0 := by
  intro h
  have := d.lt_degree_succ_nsmul hn hn0 j
  rw [h, map_zero] at this
  omega

/-- Positive multiples of a nonzero allowed degree have distinct multipliers. -/
theorem succ_nsmul_injective {n : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) :
    Function.Injective fun j : ℕ => (j + 1) • n := by
  intro i j h
  have h := congrArg d.degree h
  simp only [map_nsmul, nsmul_eq_mul] at h
  have := d.degree_pos hn hn0
  exact_mod_cast Nat.succ_injective (by exact_mod_cast mul_right_cancel₀ this.ne' h)

/-- A retained output, viewed at the cutoff equal to its degree. -/
abbrev degreeCutoffIndex {K : ℕ} (n : d.cutoff K) :
    d.cutoff (d.degree n.val).toNat :=
  ⟨n.val, d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp n.property).1, Int.self_le_toNat _⟩⟩

/-- The degree-cutoff inclusion retains the output index. -/
@[simp] theorem degreeCutoffIndex_val {K : ℕ} (n : d.cutoff K) :
    (degreeCutoffIndex d n).val = n.val := by rfl

variable {G : Type*} [AddCommGroup G] (d : PositiveDegrees G)

/-- A relative degree `m` strictly precedes `n` when it differs from it and their
positive difference is an allowed degree. -/
def Precedes (m n : G) : Prop := m ≠ n ∧ n - m ∈ d.monoid

/-- Membership in the strict relative-degree relation. -/
@[simp]
theorem precedes_iff {m n : G} : d.Precedes m n ↔ m ≠ n ∧ n - m ∈ d.monoid := Iff.rfl

/-- The strict relative-degree relation is decidable. -/
noncomputable instance instDecidablePrecedes (m n : G) : Decidable (d.Precedes m n) :=
  Classical.propDecidable _

/-- Strictly lower relative degrees have strictly smaller degree. -/
theorem degree_lt_of_precedes {m n : G} (h : d.Precedes m n) :
    d.degree m < d.degree n := by
  obtain ⟨hne, hsub⟩ := d.precedes_iff.mp h
  have hzero : n - m ≠ 0 := sub_ne_zero.mpr hne.symm
  have hpos := d.degree_pos hsub hzero
  have hsplit : m + (n - m) = n := add_sub_cancel m n
  have := congrArg d.degree hsplit
  simp only [map_add] at this
  omega

/-- A strictly preceding input also lies in the output's degree cutoff. -/
abbrev precedingDegreeCutoffIndex {K : ℕ} (n m : d.cutoff K)
    (hmn : d.Precedes m.val n.val) : d.cutoff (d.degree n.val).toNat :=
  ⟨m.val, d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp m.property).1,
    (d.degree_lt_of_precedes hmn).le.trans (Int.self_le_toNat _)⟩⟩

/-- The preceding input retains its index at the output's cutoff. -/
@[simp] theorem precedingDegreeCutoffIndex_val {K : ℕ} (n m : d.cutoff K)
    (hmn : d.Precedes m.val n.val) :
    (precedingDegreeCutoffIndex d n m hmn).val = m.val := by rfl

/-- The output-degree bound after cancelling an ambient shift. -/
theorem degree_add_val_sub_self_le (p : G) (k : ℕ) (n : d.cutoff k) :
    d.degree (p + n.val - p) ≤ k := by
  simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2

/-- The monoid membership of a retained relative degree after cancelling an ambient shift. -/
theorem add_val_sub_self_mem (p : G) (k : ℕ) (n : d.cutoff k) :
    p + n.val - p ∈ d.monoid := by
  rw [add_sub_cancel_left]
  exact (d.mem_cutoff.mp n.property).1

end TauCeti.PositiveDegrees
