/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Recursion
public import Mei.Combinatorics.Enumerative.Dyck.Vanishing
public import Mei.Combinatorics.Enumerative.RankTwoRecursion

/-!
# The shadowed grading sums solve the rank-two recursion

When `P₁` and `P₂` have constant coefficient `1`, the weight sums `C₊ = cplus` and
`C₋ = cminus` of shadowed compatible gradings of the maximal Dyck path of `(d₁, d₂)` satisfy the
initial values, the recursion (R) and the vanishing conditions (V) of
`Mei.RankTwo.IsRankTwoSolution` (`isRankTwoSolution_cplus_cminus`). With additive cancellation
(`IsCancelAdd S`),
`Mei.RankTwo.IsRankTwoSolution.unique` shows that every solution equals `(C₊, C₋)`
(`IsRankTwoSolution.eq_cplus_cminus`).

The coefficients `π_{d₂ - q, s}(P₁)` of (R) are the coefficients of `P₁ ^ (d₂ - min d₂ q)` used in
`sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus` (`rankTwoPowCoeff_sub_eq_coeff_pow`).
-/

public section

open Finset Polynomial Mei.RankTwo



namespace Mei.MaximalDyckPath

variable {S : Type*} [CommSemiring S]
variable {d₁ d₂ : ℕ} (P₁ P₂ : S[X])

/-- **`(C₊, C₋)` solves the rank-two recursion.** -/
theorem isRankTwoSolution_cplus_cminus (hP₁ : P₁.coeff 0 = 1) (hP₂ : P₂.coeff 0 = 1) :
    IsRankTwoSolution d₁ d₂ P₁ P₂ (cplus d₁ d₂ P₁ P₂) (cminus d₁ d₂ P₁ P₂) where
  plus_zero_zero := cplus_zero_zero P₁ P₂ hP₁ hP₂
  minus_zero_zero := cminus_zero_zero P₁ P₂ hP₁ hP₂
  recursion p q := by
    simp only [rankTwoPowCoeff_sub_eq_coeff_pow]
    exact sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus P₁ P₂ hP₁ hP₂ p q
  plus_eq_zero _ _ h0 hpq := cplus_eq_zero P₁ P₂ h0 hpq
  minus_eq_zero _ _ h0 hpq := cminus_eq_zero P₁ P₂ h0 hpq

/-- **With additive cancellation, every solution of the rank-two recursion is `(C₊, C₋)`.** -/
theorem _root_.Mei.RankTwo.IsRankTwoSolution.eq_cplus_cminus [IsCancelAdd S] {P₁ P₂ : S[X]}
    {Cp Cm : ℕ → ℕ → S} (h : IsRankTwoSolution d₁ d₂ P₁ P₂ Cp Cm) (hP₁ : P₁.coeff 0 = 1)
    (hP₂ : P₂.coeff 0 = 1) : Cp = cplus d₁ d₂ P₁ P₂ ∧ Cm = cminus d₁ d₂ P₁ P₂ :=
  h.unique (isRankTwoSolution_cplus_cminus P₁ P₂ hP₁ hP₂) hP₁ hP₂

end Mei.MaximalDyckPath
