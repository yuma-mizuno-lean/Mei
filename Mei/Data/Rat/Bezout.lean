/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Bezout for rational scalings

If a positive rational `K` scales two integers `b` and `-a` to integers, then `K gcd(a, b)` is a
natural number, by Bezout's identity.
-/

public section

namespace Mei

/-- **Bezout for rational scalings.** If `K > 0` makes `K b` and `-K a` integers `k₁` and `k₂`, then
`K gcd(a, b) = k₁ gcdB(a, b) - k₂ gcdA(a, b)` is a natural number. -/
theorem exists_natCast_eq_mul_gcd {K : ℚ} (hK : 0 < K) {a b k₁ k₂ : ℤ}
    (hg : 0 < Int.gcd a b) (h₁ : K * b = k₁) (h₂ : K * a = -k₂) :
    ∃ z : ℕ, (z : ℚ) = K * Int.gcd a b := by
  have hbezQ : (Int.gcd a b : ℚ) = a * Int.gcdA a b + b * Int.gcdB a b := by
    exact_mod_cast Int.gcd_eq_gcd_ab a b
  have hK : K * (Int.gcd a b : ℚ) = ((k₁ * Int.gcdB a b - k₂ * Int.gcdA a b : ℤ) : ℚ) := by
    rw [hbezQ]
    push_cast
    linear_combination (Int.gcdA a b : ℚ) * h₂ + (Int.gcdB a b : ℚ) * h₁
  have hpos : 0 < k₁ * Int.gcdB a b - k₂ * Int.gcdA a b := by
    have : (0 : ℚ) < ((k₁ * Int.gcdB a b - k₂ * Int.gcdA a b : ℤ) : ℚ) := by
      rw [← hK]
      have : (0 : ℚ) < Int.gcd a b := by exact_mod_cast hg
      positivity
    exact_mod_cast this
  refine ⟨(k₁ * Int.gcdB a b - k₂ * Int.gcdA a b).toNat, ?_⟩
  rw [hK]
  exact_mod_cast Int.toNat_of_nonneg hpos.le

end Mei
