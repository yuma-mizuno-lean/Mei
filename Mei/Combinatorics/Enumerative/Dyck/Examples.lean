/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Recursion
public import Mei.Combinatorics.Enumerative.Dyck.Tight
import Mathlib.Tactic.LinearCombination

/-!
# Worked examples of the rank-two Dyck-grading sums

Take `P₁ = 1 + a x + b x²` and `P₂ = 1 + c y + d y²`. The weight sums of shadowed and tight
gradings of the maximal Dyck paths (`shadowedSum`, `tightSum`) are polynomials in `a, b, c, d`.
Burcroff–Lee–Mou express the coefficients of the rank-two wall functions through these sums. In
the diagonal direction `(a, b) = (1, 1)` of their notation, the degree-`k` coefficient of the wall
function `f(u)` is the tight sum with totals `(k, k)` of a rectangle `(d₁, d₂)` with
`d₁ - d₂ = 1` and `d₁, d₂ ≥ k` (their Remark 5.20), and the degree-`k` coefficient of `f ^ m` is the
shadowed sum with totals `(k, k)` of a one-bending rectangle with `m = |d₁ - d₂|` and
`d₁, d₂ ≥ k` (their Theorem 5.17). This file evaluates these sums on three rectangles.

* `tightSum_four_three_one_one`, `tightSum_four_three_two_two`, `tightSum_four_three_three_three`:
  on the rectangle `(4, 3)`, the tight sums with totals `(k, k)` for `k ≤ 3`, the first three
  coefficients of `f`, are `a c`, `2 b d + b c² + a² d` and `5 a b c d`.
* `shadowedSum_six_four_three_three`: on the rectangle `(6, 4)`, which is one-bending by the
  lattice test although `d₂ < m k`, the shadowed sum with totals `(3, 3)` is
  `14 a b c d + 2 a b c³ + 2 a³ c d`. This is the degree-`3` coefficient of the square of the
  series with the coefficients of `f` above
  (`shadowedSum_six_four_three_three_eq_coeff_sq`).
* `shadowedSum_five_three_three_three`: on the rectangle `(5, 3)`, which is not one-bending, the
  shadowed sum with totals `(3, 3)` is `16 a b c d + 2 a b c³ + 2 a³ c d`. It exceeds the sum
  of `(6, 4)` by `2 a b c d` (`shadowedSum_five_three_sub_six_four`), the contribution that
  one-bending excludes.

The values are computed from the recursion (R) and the vanishing conditions (V) of
`Mei.MaximalDyckPath.sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus`: for every `(p, q)` with
`p, q ≤ 3`, (R) solves for the one of `C₊(p, q)` and `C₋(p, q)` that (V) does not kill, in terms
of the values at smaller `p + q`.

## References

* Amanda Burcroff, Kyungyong Lee, Lang Mou, *Positivity of generalized cluster scattering
  diagrams*, Remark 5.20 and Theorem 5.17, arXiv:2503.03719v1.
-/

public section

open Finset Polynomial

namespace Mei.MaximalDyckPath

variable {S : Type*} [CommRing S] (a b c d : S)

/-- The polynomial `1 + a x + b x²`, kept opaque so that its coefficient lemmas fire as simp
lemmas. -/
private noncomputable def quad : S[X] := 1 + C a * X + C b * X ^ 2

private theorem quad_eq : quad a b = 1 + C a * X + C b * X ^ 2 := (rfl)

@[simp]
private theorem coeff_quad_zero : (quad a b).coeff 0 = 1 := by
  simp [quad, coeff_one]

@[simp]
private theorem coeff_quad_one : (quad a b).coeff 1 = a := by
  simp [quad, coeff_one]

@[simp]
private theorem coeff_quad_two : (quad a b).coeff 2 = b := by
  simp [quad, coeff_one]

@[simp]
private theorem coeff_quad_add_three (n : ℕ) : (quad a b).coeff (n + 3) = 0 := by
  simp [quad, coeff_one]

@[simp]
private theorem coeff_quad_pow_zero (n : ℕ) : (quad a b ^ n).coeff 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, mul_coeff_zero, ih]

@[simp]
private theorem coeff_quad_pow_one (n : ℕ) : (quad a b ^ n).coeff 1 = n * a := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    simp [pow_succ', coeff_mul, Finset.Nat.antidiagonal_succ, ih, coeff_quad_pow_zero]
    ring

@[simp]
private theorem coeff_quad_pow_two (n : ℕ) :
    (quad a b ^ n).coeff 2 = n.choose 2 * a ^ 2 + n * b := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    simp [pow_succ', coeff_mul, Finset.Nat.antidiagonal_succ, ih, coeff_quad_pow_zero,
      coeff_quad_pow_one, Nat.choose_succ_succ]
    ring

@[simp]
private theorem coeff_quad_pow_three (n : ℕ) :
    (quad a b ^ n).coeff 3 = n.choose 3 * a ^ 3 + 2 * n.choose 2 * a * b := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    simp [pow_succ', coeff_mul, Finset.Nat.antidiagonal_succ, ih, coeff_quad_pow_one,
      coeff_quad_pow_two, Nat.choose_succ_succ]
    ring

attribute [local simp] Nat.choose coeff_one

/-! ### The rectangle `(4, 3)` -/

/-- The values `C₊(k, k)`, `k = 1, 2, 3`, on the rectangle `(4, 3)`. Each step of the proof
solves (R) at `(p, q)` for the unknown `C₊(p, q)` or `C₋(p, q)`, the other being zero by (V); the
steps run through the pairs with `p, q ≤ 3` in order of `p + q`. -/
private theorem cplus_four_three :
    cplus 4 3 (quad a b) (quad c d) 1 1 = a * c ∧
    cplus 4 3 (quad a b) (quad c d) 2 2 = a ^ 2 * d + b * c ^ 2 + 2 * b * d ∧
    cplus 4 3 (quad a b) (quad c d) 3 3 = 5 * a * b * c * d := by
  have R := sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus (d₁ := 4) (d₂ := 3) (quad a b) (quad c d)
    (coeff_quad_zero a b) (coeff_quad_zero c d)
  have cp01 : cplus 4 3 (quad a b) (quad c d) 0 1 = 4 * c := by
    have h := R 0 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm10 : cminus 4 3 (quad a b) (quad c d) 1 0 = 3 * a := by
    have h := R 1 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp02 : cplus 4 3 (quad a b) (quad c d) 0 2 = 6 * c ^ 2 + 4 * d := by
    have h := R 0 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp11 : cplus 4 3 (quad a b) (quad c d) 1 1 = a * c := by
    have h := R 1 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm20 : cminus 4 3 (quad a b) (quad c d) 2 0 = 3 * a ^ 2 + 3 * b := by
    have h := R 2 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp03 : cplus 4 3 (quad a b) (quad c d) 0 3 = 4 * c ^ 3 + 12 * c * d := by
    have h := R 0 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp12 : cplus 4 3 (quad a b) (quad c d) 1 2 = 3 * a * c ^ 2 + 5 * a * d := by
    have h := R 1 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm21 : cminus 4 3 (quad a b) (quad c d) 2 1 = 2 * b * c := by
    have h := R 2 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cm30 : cminus 4 3 (quad a b) (quad c d) 3 0 = a ^ 3 + 6 * a * b := by
    have h := R 3 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp13 : cplus 4 3 (quad a b) (quad c d) 1 3 = 3 * a * c ^ 3 + 18 * a * c * d := by
    have h := R 1 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp22 : cplus 4 3 (quad a b) (quad c d) 2 2 = a ^ 2 * d + b * c ^ 2 + 2 * b * d := by
    have h := R 2 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm31 : cminus 4 3 (quad a b) (quad c d) 3 1 = 4 * a * b * c := by
    have h := R 3 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp23 :
      cplus 4 3 (quad a b) (quad c d) 2 3 =
        6 * a ^ 2 * c * d + 2 * b * c ^ 3 + 10 * b * c * d := by
    have h := R 2 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm32 : cminus 4 3 (quad a b) (quad c d) 3 2 = a * b * d := by
    have h := R 3 2
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp33 : cplus 4 3 (quad a b) (quad c d) 3 3 = 5 * a * b * c * d := by
    have h := R 3 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  exact ⟨cp11, cp22, cp33⟩

/-! ### The rectangle `(5, 3)` -/

/-- The value `C₊(3, 3)` on the rectangle `(5, 3)`, computed as for `(4, 3)`. -/
private theorem cplus_five_three :
    cplus 5 3 (quad a b) (quad c d) 3 3 =
      2 * a ^ 3 * c * d + 2 * a * b * c ^ 3 + 16 * a * b * c * d := by
  have R := sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus (d₁ := 5) (d₂ := 3) (quad a b) (quad c d)
    (coeff_quad_zero a b) (coeff_quad_zero c d)
  have cp01 : cplus 5 3 (quad a b) (quad c d) 0 1 = 5 * c := by
    have h := R 0 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm10 : cminus 5 3 (quad a b) (quad c d) 1 0 = 3 * a := by
    have h := R 1 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp02 : cplus 5 3 (quad a b) (quad c d) 0 2 = 10 * c ^ 2 + 5 * d := by
    have h := R 0 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp11 : cplus 5 3 (quad a b) (quad c d) 1 1 = 2 * a * c := by
    have h := R 1 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm20 : cminus 5 3 (quad a b) (quad c d) 2 0 = 3 * a ^ 2 + 3 * b := by
    have h := R 2 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp03 : cplus 5 3 (quad a b) (quad c d) 0 3 = 10 * c ^ 3 + 20 * c * d := by
    have h := R 0 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp12 : cplus 5 3 (quad a b) (quad c d) 1 2 = 8 * a * c ^ 2 + 7 * a * d := by
    have h := R 1 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm21 : cminus 5 3 (quad a b) (quad c d) 2 1 = b * c := by
    have h := R 2 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cm30 : cminus 5 3 (quad a b) (quad c d) 3 0 = a ^ 3 + 6 * a * b := by
    have h := R 3 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp13 : cplus 5 3 (quad a b) (quad c d) 1 3 = 12 * a * c ^ 3 + 36 * a * c * d := by
    have h := R 1 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp22 :
      cplus 5 3 (quad a b) (quad c d) 2 2 =
        a ^ 2 * c ^ 2 + 2 * a ^ 2 * d + 2 * b * c ^ 2 + 4 * b * d := by
    have h := R 2 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm31 : cminus 5 3 (quad a b) (quad c d) 3 1 = 2 * a * b * c := by
    have h := R 3 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp23 :
      cplus 5 3 (quad a b) (quad c d) 2 3 =
        3 * a ^ 2 * c ^ 3 + 18 * a ^ 2 * c * d + 6 * b * c ^ 3 + 21 * b * c * d := by
    have h := R 2 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp32 : cplus 5 3 (quad a b) (quad c d) 3 2 = a * b * d := by
    have h := R 3 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp33 :
      cplus 5 3 (quad a b) (quad c d) 3 3 =
        2 * a ^ 3 * c * d + 2 * a * b * c ^ 3 + 16 * a * b * c * d := by
    have h := R 3 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  exact cp33

/-! ### The rectangle `(6, 4)` -/

/-- The value `C₊(3, 3)` on the rectangle `(6, 4)`, computed as for `(4, 3)`. -/
private theorem cplus_six_four :
    cplus 6 4 (quad a b) (quad c d) 3 3 =
      2 * a ^ 3 * c * d + 2 * a * b * c ^ 3 + 14 * a * b * c * d := by
  have R := sum_coeff_mul_cplus_eq_sum_coeff_mul_cminus (d₁ := 6) (d₂ := 4) (quad a b) (quad c d)
    (coeff_quad_zero a b) (coeff_quad_zero c d)
  have cp01 : cplus 6 4 (quad a b) (quad c d) 0 1 = 6 * c := by
    have h := R 0 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm10 : cminus 6 4 (quad a b) (quad c d) 1 0 = 4 * a := by
    have h := R 1 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp02 : cplus 6 4 (quad a b) (quad c d) 0 2 = 15 * c ^ 2 + 6 * d := by
    have h := R 0 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp11 : cplus 6 4 (quad a b) (quad c d) 1 1 = 2 * a * c := by
    have h := R 1 1
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm20 : cminus 6 4 (quad a b) (quad c d) 2 0 = 6 * a ^ 2 + 4 * b := by
    have h := R 2 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp03 : cplus 6 4 (quad a b) (quad c d) 0 3 = 20 * c ^ 3 + 30 * c * d := by
    have h := R 0 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp12 : cplus 6 4 (quad a b) (quad c d) 1 2 = 10 * a * c ^ 2 + 8 * a * d := by
    have h := R 1 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm21 : cminus 6 4 (quad a b) (quad c d) 2 1 = 2 * b * c := by
    have h := R 2 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cm30 : cminus 6 4 (quad a b) (quad c d) 3 0 = 4 * a ^ 3 + 12 * a * b := by
    have h := R 3 0
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp13 : cplus 6 4 (quad a b) (quad c d) 1 3 = 20 * a * c ^ 3 + 50 * a * c * d := by
    have h := R 1 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp22 :
      cplus 6 4 (quad a b) (quad c d) 2 2 =
        a ^ 2 * c ^ 2 + 2 * a ^ 2 * d + 2 * b * c ^ 2 + 4 * b * d := by
    have h := R 2 2
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cm31 : cminus 6 4 (quad a b) (quad c d) 3 1 = 6 * a * b * c := by
    have h := R 3 1
    simp [sum_range_succ, *, -R] at h
    linear_combination -h
  have cp23 :
      cplus 6 4 (quad a b) (quad c d) 2 3 =
        4 * a ^ 2 * c ^ 3 + 22 * a ^ 2 * c * d + 8 * b * c ^ 3 + 26 * b * c * d := by
    have h := R 2 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  have cp33 :
      cplus 6 4 (quad a b) (quad c d) 3 3 =
        2 * a ^ 3 * c * d + 2 * a * b * c ^ 3 + 14 * a * b * c * d := by
    have h := R 3 3
    simp [sum_range_succ, *, -R] at h
    linear_combination h
  exact cp33

/-! ### Consequences for tight and shadowed sums -/

private theorem tightSum_four_three_eq_cplus {k : ℕ} (hk : k ≤ 3) :
    tightSum 4 3 (quad a b) (quad c d) k k = cplus 4 3 (quad a b) (quad c d) k k := by
  simpa using tightSum_mul_eq_cplus (d₁ := 4) (d₂ := 3) (quad a b) (quad c d) (a := 1) (b := 1)
    (k := k) (by norm_num) (by omega) (by omega)

/-- On the rectangle `(4, 3)`, the tight sum with totals `(1, 1)` is `a c`. By the coefficient
formula of Burcroff–Lee–Mou (Remark 5.20) this is the coefficient of `u` in the diagonal wall
function of `P₁ = 1 + a x + b x²` and `P₂ = 1 + c y + d y²`. -/
theorem tightSum_four_three_one_one :
    tightSum 4 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 1 1 = a * c := by
  rw [← quad_eq, ← quad_eq, tightSum_four_three_eq_cplus a b c d (by norm_num)]
  exact (cplus_four_three a b c d).1

/-- On the rectangle `(4, 3)`, the tight sum with totals `(2, 2)` is `2 b d + b c² + a² d`,
the coefficient of `u ^ 2` in the diagonal wall function (Burcroff–Lee–Mou, Remark 5.20). -/
theorem tightSum_four_three_two_two :
    tightSum 4 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 2 2 =
      2 * b * d + b * c ^ 2 + a ^ 2 * d := by
  rw [← quad_eq, ← quad_eq, tightSum_four_three_eq_cplus a b c d (by norm_num),
    (cplus_four_three a b c d).2.1]
  ring

/-- On the rectangle `(4, 3)`, the tight sum with totals `(3, 3)` is `5 a b c d`, the coefficient
of `u ^ 3` in the diagonal wall function (Burcroff–Lee–Mou, Remark 5.20). -/
theorem tightSum_four_three_three_three :
    tightSum 4 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 =
      5 * a * b * c * d := by
  rw [← quad_eq, ← quad_eq, tightSum_four_three_eq_cplus a b c d (by norm_num),
    (cplus_four_three a b c d).2.2]

/-- On the one-bending rectangle `(6, 4)`, the shadowed sum with totals `(3, 3)` is
`14 a b c d + 2 a b c³ + 2 a³ c d`. -/
theorem shadowedSum_six_four_three_three :
    shadowedSum 6 4 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 =
      14 * a * b * c * d + 2 * a * b * c ^ 3 + 2 * a ^ 3 * c * d := by
  rw [← quad_eq, ← quad_eq, shadowedSum_eq_cplus _ _ (by norm_num), cplus_six_four]
  ring

/-- On the rectangle `(5, 3)`, which is not one-bending, the shadowed sum with totals `(3, 3)` is
`16 a b c d + 2 a b c³ + 2 a³ c d`. -/
theorem shadowedSum_five_three_three_three :
    shadowedSum 5 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 =
      16 * a * b * c * d + 2 * a * b * c ^ 3 + 2 * a ^ 3 * c * d := by
  rw [← quad_eq, ← quad_eq, shadowedSum_eq_cplus _ _ (by norm_num), cplus_five_three]
  ring

/-- The shadowed sum of `(5, 3)` with totals `(3, 3)` exceeds that of `(6, 4)` by `2 a b c d`. -/
theorem shadowedSum_five_three_sub_six_four :
    shadowedSum 5 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 -
      shadowedSum 6 4 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 =
        2 * a * b * c * d := by
  rw [shadowedSum_five_three_three_three, shadowedSum_six_four_three_three]
  ring

/-- On the rectangle `(6, 4)`, the shadowed sum with totals `(3, 3)` is the degree-`3`
coefficient of the square of the series `∑ₖ tightSum(k, k) uᵏ` whose coefficients are the tight
sums of the rectangle `(4, 3)`, truncated at degree `3`. -/
theorem shadowedSum_six_four_three_three_eq_coeff_sq :
    shadowedSum 6 4 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 3 3 =
      ((∑ k ∈ range 4, C (tightSum 4 3 (1 + C a * X + C b * X ^ 2)
        (1 + C c * X + C d * X ^ 2) k k) * X ^ k) ^ 2).coeff 3 := by
  have h0 : tightSum 4 3 (1 + C a * X + C b * X ^ 2) (1 + C c * X + C d * X ^ 2) 0 0 = 1 := by
    rw [← quad_eq, ← quad_eq, tightSum_four_three_eq_cplus a b c d (by norm_num)]
    simp
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, h0, tightSum_four_three_one_one,
    tightSum_four_three_two_two, tightSum_four_three_three_three,
    shadowedSum_six_four_three_three]
  simp [sq, coeff_mul, Finset.Nat.antidiagonal_succ, coeff_X_pow, coeff_X, coeff_one]
  ring

end Mei.MaximalDyckPath
