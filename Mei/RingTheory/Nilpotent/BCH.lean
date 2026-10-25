/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Nilpotent.Log
public import Mei.RingTheory.Ideal.Operations
public import Mei.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# The Baker–Campbell–Hausdorff formula through degree three

For elements of a left ideal whose fourth power vanishes, the finite logarithm of the
product of their finite exponentials is exactly the usual BCH polynomial through degree three.
All longer words vanish by the ideal-power assumption; no convergence assumption is involved.

The exponential identity expresses multiplication of exponentials in terms of the BCH
polynomial. The ideal-membership lemmas ensure that this product differs from one by an
element of the nilpotent ideal, so its finite logarithm applies and recovers that polynomial.
The finite exponential and logarithm are supplied by `IsNilpotent.exp_eq_sum` and
`IsNilpotent.log_eq_sum`, with inverse identity `IsNilpotent.exp_log`.
-/

public section

namespace Ideal
variable {A : Type*} [Ring A]

variable [Algebra ℚ A]

-- Separate the homogeneous terms before expanding the powers of the logarithm.
private theorem algebra_bch3 (x y : A)
    (h4 : ∀ a b c d : A, (a = x ∨ a = y) → (b = x ∨ b = y) →
      (c = x ∨ c = y) → (d = x ∨ d = y) → a * (b * (c * d)) = 0) :
    let e := (1 + x + (1 / 2 : ℚ) • x ^ 2 + (1 / 6 : ℚ) • x ^ 3) *
      (1 + y + (1 / 2 : ℚ) • y ^ 2 + (1 / 6 : ℚ) • y ^ 3) - 1
    e - (1 / 2 : ℚ) • e ^ 2 + (1 / 3 : ℚ) • e ^ 3 =
      x + y + (1 / 2 : ℚ) • (x * y - y * x) +
        (1 / 12 : ℚ) • ((x * (x * y - y * x) - (x * y - y * x) * x) +
          (y * (y * x - x * y) - (y * x - x * y) * y)) := by
  have hxxxx : x * (x * (x * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxxxy : x * (x * (x * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxxyx : x * (x * (y * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxxyy : x * (x * (y * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxyxx : x * (y * (x * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxyxy : x * (y * (x * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxyyx : x * (y * (y * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hxyyy : x * (y * (y * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyxxx : y * (x * (x * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyxxy : y * (x * (x * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyxyx : y * (x * (y * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyxyy : y * (x * (y * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyyxx : y * (y * (x * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyyxy : y * (y * (x * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyyyx : y * (y * (y * x)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hyyyy : y * (y * (y * y)) = 0 := h4 _ _ _ _ (by simp) (by simp) (by simp) (by simp)
  -- Products of total degree at least four vanish, so square and cube reduce separately.
  let l := x + y
  let q := (1 / 2 : ℚ) • x ^ 2 + x * y + (1 / 2 : ℚ) • y ^ 2
  let c := (1 / 6 : ℚ) • x ^ 3 + (1 / 2 : ℚ) • (x ^ 2 * y) +
    (1 / 2 : ℚ) • (x * y ^ 2) + (1 / 6 : ℚ) • y ^ 3
  have he : (1 + x + (1 / 2 : ℚ) • x ^ 2 + (1 / 6 : ℚ) • x ^ 3) *
      (1 + y + (1 / 2 : ℚ) • y ^ 2 + (1 / 6 : ℚ) • y ^ 3) - 1 = l + q + c := by
    dsimp [l, q, c]
    noncomm_ring [hxxxx, hxxxy, hxxyx, hxxyy, hxyxx, hxyxy, hxyyx, hxyyy,
      hyxxx, hyxxy, hyxyx, hyxyy, hyyxx, hyyxy, hyyyx, hyyyy, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  have he2 : (l + q + c) ^ 2 = l ^ 2 + l * q + q * l := by
    dsimp [l, q, c]
    noncomm_ring [hxxxx, hxxxy, hxxyx, hxxyy, hxyxx, hxyxy, hxyyx, hxyyy,
      hyxxx, hyxxy, hyxyx, hyxyy, hyyxx, hyyxy, hyyyx, hyyyy, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  have he3 : (l + q + c) ^ 3 = l ^ 3 := by
    rw [pow_succ, he2]
    dsimp [l, q, c]
    noncomm_ring [hxxxx, hxxxy, hxxyx, hxxyy, hxyxx, hxyxy, hxyyx, hxyyy,
      hyxxx, hyxxy, hyxyx, hyxyy, hyyxx, hyyxy, hyyyx, hyyyy, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  dsimp only
  rw [he, he2, he3]
  dsimp [l, q, c]
  noncomm_ring [smul_add, smul_sub, smul_smul, smul_neg, add_smul, sub_smul]
  module

/-- The Baker–Campbell–Hausdorff formula is exact through degree three in a
nilpotent ideal whose fourth power vanishes. -/
theorem log_exp_mul_exp_of_pow_four_eq_bot (I : Ideal A)
    (hI : I ^ 4 = ⊥) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    IsNilpotent.log (IsNilpotent.exp x * IsNilpotent.exp y) =
      x + y + (1 / 2 : ℚ) • (x * y - y * x) +
        (1 / 12 : ℚ) • ((x * (x * y - y * x) - (x * y - y * x) * x) +
          (y * (y * x - x * y) - (y * x - x * y) * y)) := by
  have hI0 : I ^ 4 = 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hx4 := Ideal.pow_eq_zero_of_mem hI0 le_rfl hx
  have hy4 := Ideal.pow_eq_zero_of_mem hI0 le_rfl hy
  have hu := I.exp_mul_exp_sub_one_mem hx hy ⟨4, hx4⟩ ⟨4, hy4⟩
  have hu4 := Ideal.pow_eq_zero_of_mem hI0 le_rfl hu
  rw [IsNilpotent.log_eq_sum hu4, IsNilpotent.exp_eq_sum hx4,
    IsNilpotent.exp_eq_sum hy4]
  have hp := algebra_bch3 x y (fun a b c d ha hb hc hd ↦ by
    have ha' : a ∈ I := ha.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hb' : b ∈ I := hb.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hc' : c ∈ I := hc.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hd' : d ∈ I := hd.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    simpa only [mul_assoc] using
      I.mul_four_eq_zero_of_pow_eq_bot hI ha' hb' hc' hd')
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp ⊢
  convert hp using 1; module

/-- Exponentiating the degree-three BCH polynomial gives the product of exponentials. -/
theorem exp_bch_of_pow_four_eq_bot (I : Ideal A)
    (hI : I ^ 4 = ⊥) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    IsNilpotent.exp (x + y + (1 / 2 : ℚ) • (x * y - y * x) +
        (1 / 12 : ℚ) • ((x * (x * y - y * x) - (x * y - y * x) * x) +
          (y * (y * x - x * y) - (y * x - x * y) * y))) =
      IsNilpotent.exp x * IsNilpotent.exp y := by
  have hI0 : I ^ 4 = 0 := by simpa only [Ideal.zero_eq_bot] using hI
  rw [← log_exp_mul_exp_of_pow_four_eq_bot I hI hx hy]
  apply IsNilpotent.exp_log
  refine ⟨4, ?_⟩
  exact Ideal.pow_eq_zero_of_mem hI0 le_rfl
    (I.exp_mul_exp_sub_one_mem hx hy
      ⟨4, Ideal.pow_eq_zero_of_mem hI0 le_rfl hx⟩
      ⟨4, Ideal.pow_eq_zero_of_mem hI0 le_rfl hy⟩)

end Ideal
