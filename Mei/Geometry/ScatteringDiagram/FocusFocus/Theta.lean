/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.RingTheory.Node.SignedMonomial

/-!
# Theta functions of the focus-focus algebra

For a commutative ring `S` and `t : S`, the coordinate ring of the focus-focus singularity
is the slab algebra `S[W^{±1}][X,Y]/(XY - t(1+W))`. In the Gross–Siebert description of this
singularity its theta functions are the monomials `ϑ_{n,b} = X^(-n) W^b` for `n ≤ 0` and
`ϑ_{n,b} = Y^n W^b` for `n ≥ 0`; this file defines these elements and computes their products.

They form an `S`-basis indexed by `ℤ × ℤ` (`Mei.NodeAlgebra.laurentBasis`), so the algebra is
free, hence flat, over `S`. They multiply by
`ϑ_{n,b} ϑ_{m,c} = t^r ∑_{j=0}^r (r choose j) ϑ_{n+m,b+c+j}` with
`r = (|n| + |m| - |n + m|) / 2`. The structure constants `(r choose j) t^r` are images of
elements of `ℕ[t]`.

The usual truncated coefficient ring is `S = K[t]/(t^(k+1))`; here `S` and `t` are arbitrary.
The example follows Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public section

noncomputable section

namespace Mei.FocusFocus

open TauCeti TauCeti.NodeAlgebra LaurentPolynomial Mei.NodeAlgebra
open scoped Mei.NodeAlgebra

variable {S : Type*} [CommRing S] (t : S)

/-- The theta function `ϑ_{n,b}` of the focus-focus algebra `S[W^{±1}][X,Y]/(XY - t(1+W))`:
`X^(-n) W^b` for `n ≤ 0` and `Y^n W^b` for `n ≥ 0`. -/
def theta (n b : ℤ) : NodeAlgebra S[T;T⁻¹] (C t * (1 + T 1)) :=
  (T b : S[T;T⁻¹]) • signedMonomial (C t * (1 + T 1)) n

/-- `ϑ_{n,b}` is `W^b` times the signed monomial of `n`. -/
theorem theta_def (n b : ℤ) :
    theta t n b = (T b : S[T;T⁻¹]) • signedMonomial (C t * (1 + T 1)) n :=
  (rfl)

/-- For a natural number `n`, `ϑ_{n,b} = Y^n W^b`. -/
@[simp]
theorem theta_natCast (n : ℕ) (b : ℤ) :
    theta t n b = (T b : S[T;T⁻¹]) • coord (C t * (1 + T 1)) 1 ^ n := by
  rw [theta_def, signedMonomial_natCast]

/-- For a natural number `n`, `ϑ_{-n,b} = X^n W^b`. -/
@[simp]
theorem theta_neg_natCast (n : ℕ) (b : ℤ) :
    theta t (-n) b = (T b : S[T;T⁻¹]) • coord (C t * (1 + T 1)) 0 ^ n := by
  rw [theta_def, signedMonomial_neg_natCast]

/-- The theta functions are the vectors of the `S`-basis `laurentBasis` of the focus-focus
algebra. -/
theorem laurentBasis_apply_eq_theta (n b : ℤ) :
    laurentBasis (C t * (1 + T 1)) (n, b) = theta t n b :=
  laurentBasis_apply _ n b

/-- The theta function `ϑ_{0,0}` is `1`. -/
@[simp]
theorem theta_zero_zero : theta t 0 0 = 1 := by
  simp [theta_def]

/-- Multiplication of focus-focus theta functions:
`ϑ_{n,b} ϑ_{m,c} = t^r ∑_{j=0}^r (r choose j) ϑ_{n+m,b+c+j}`, where
`r = (|n| + |m| - |n + m|) / 2`. -/
theorem theta_mul_theta (n m b c : ℤ) :
    theta t n b * theta t m c =
      t ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) •
        ∑ j ∈ Finset.range ((n.natAbs + m.natAbs - (n + m).natAbs) / 2 + 1),
          ((n.natAbs + m.natAbs - (n + m).natAbs) / 2).choose j •
            theta t (n + m) (b + c + j) := by
  set r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
  -- Both sides are a Laurent coefficient times the signed monomial of `n + m`.
  have hcoeff : (T (b + c) : S[T;T⁻¹]) * (C t * (1 + T 1)) ^ r =
      ∑ j ∈ Finset.range (r + 1), t ^ r • r.choose j • (T (b + c + j) : S[T;T⁻¹]) := by
    rw [mul_pow, add_comm (1 : S[T;T⁻¹]), add_pow, ← map_pow C]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [T_pow, smul_eq_C_mul, nsmul_eq_mul, one_pow, mul_one, T_add]
    ring
  calc
    theta t n b * theta t m c =
        ((T (b + c) : S[T;T⁻¹]) * (C t * (1 + T 1)) ^ r) •
          signedMonomial (C t * (1 + T 1)) (n + m) := by
      simp only [theta_def, smul_mul_smul_comm]
      rw [signedMonomial_mul_signedMonomial, ← map_pow]
      simp only [← Algebra.smul_def, smul_smul, T_add, r]
    _ = _ := by
      rw [hcoeff]
      simp only [Finset.sum_smul, Finset.smul_sum, theta_def, smul_assoc]

/-- The product `ϑ_{-1,0} ϑ_{1,0} = XY` is `t ϑ_{0,0} + t ϑ_{0,1}`. -/
theorem theta_neg_one_mul_theta_one :
    theta t (-1) 0 * theta t 1 0 = t • theta t 0 0 + t • theta t 0 1 := by
  rw [theta_mul_theta]
  norm_num [Finset.sum_range_succ]

end Mei.FocusFocus
