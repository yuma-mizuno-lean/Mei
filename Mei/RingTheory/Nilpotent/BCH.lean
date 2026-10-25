/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Nilpotent.Log
public import Mei.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# The Baker–Campbell–Hausdorff formula through degree three

For elements of a left ideal whose fourth power vanishes, the finite logarithm of the
product of their finite exponentials is exactly the usual BCH polynomial through degree three.
All longer words vanish by the ideal-power assumption; no convergence assumption is involved.

The proof uses `IsNilpotent.exp_eq_sum`, `IsNilpotent.log_eq_sum`, and the inverse
identity `IsNilpotent.exp_log`. The degree-three polynomial is verified by direct expansion.
-/

public section

namespace Ideal
variable {A : Type*} [Ring A]

private theorem mul_four_eq_zero_of_pow_eq_bot (I : Ideal A) (hI : I ^ 4 = ⊥)
    {a b c d : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I) :
    a * b * c * d = 0 := by
  have h := Ideal.mul_mem_mul (Ideal.mul_mem_mul (Ideal.mul_mem_mul ha hb) hc) hd
  -- Expand the fixed numeral power with the left-associated ideal-power convention.
  have he : ((I * I) * I) * I = I ^ 4 := by
    simp only [show (4 : ℕ) = 3 + 1 from rfl, Submodule.pow_succ,
      show (3 : ℕ) = 2 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
      Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_mul]
  rwa [he, hI, Ideal.mem_bot] at h

variable [Algebra ℚ A]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- The cubic expansion contains many words before the degree-four reductions.
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
  dsimp only
  noncomm_ring [hxxxx, hxxxy, hxxyx, hxxyy, hxyxx, hxyxy, hxyyx, hxyyy,
    hyxxx, hyxxy, hyxyx, hyxyy, hyyxx, hyyxy, hyyyx, hyyyy, smul_add, smul_sub, smul_smul,
    smul_neg, add_smul, sub_smul]
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
