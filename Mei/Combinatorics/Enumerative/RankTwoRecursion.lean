/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# The rank-two recursion for Dyck-grading sums

For polynomials `P₁, P₂` and `r : ℤ`, `s : ℕ`, put `π_{r,s}(P) = [z^s] P(z)^r` for `r ≥ 0`,
`π_{r,0}(P) = 1` for `r < 0` and `π_{r,s}(P) = 0` for `r < 0 < s` (`rankTwoPowCoeff`).
A pair of coefficient families `C₊, C₋ : ℕ → ℕ → S` is an `IsRankTwoSolution` for `(d₁, d₂)`
if `C₊(0, 0) = C₋(0, 0) = 1`, it satisfies the recursion

  `∑_{s=0}^{p} π_{d₂-q,s}(P₁) C₊(p-s, q) = ∑_{s=0}^{q} π_{d₁-p,s}(P₂) C₋(p, q-s)`   (R)

for all `(p, q)`, and off `(0, 0)` the vanishing conditions (V): `C₊(p, q) = 0` when
`d₁ q ≤ d₂ p` and `C₋(p, q) = 0` when `d₁ q ≥ d₂ p`.

When the constant coefficients of `P₁` and `P₂` are `1`, an `IsRankTwoSolution` is unique: the
`s = 0` terms of (R) are `C₊(p, q)` and `C₋(p, q)`, all other terms have smaller total degree,
and (V) kills one of the two new values. Hence two families satisfying (R), (V) and the initial
values coincide, by induction on `p + q`. The definitions and recursion work over any
semiring; uniqueness additionally requires additive cancellation.

The vanishing conditions (V) and recursion (R) for shadowed grading sums are from
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Lemmas 5.23 and
5.27, respectively (https://arxiv.org/html/2503.03719v1). Corollary 5.29 records the same
identities for their polynomials `d₊` and `d₋`; it does not state uniqueness. The uniqueness
theorem here is the elementary induction on `p + q` described above.
-/

public section

open Finset Polynomial

namespace Polynomial

variable {S : Type*} [Semiring S]

/-- `π_{r,s}(P)`: the coefficient of `z^s` in `P^r` for `r ≥ 0`; for `r < 0` it is `1` at
`s = 0` and `0` otherwise. -/
noncomputable def rankTwoPowCoeff (P : S[X]) (r : ℤ) (s : ℕ) : S :=
  if 0 ≤ r then (P ^ r.toNat).coeff s else if s = 0 then 1 else 0

@[simp]
theorem rankTwoPowCoeff_of_nonneg (P : S[X]) {r : ℤ} (hr : 0 ≤ r) (s : ℕ) :
    rankTwoPowCoeff P r s = (P ^ r.toNat).coeff s := by
  simp [rankTwoPowCoeff, hr]

@[simp]
theorem rankTwoPowCoeff_of_neg (P : S[X]) {r : ℤ} (hr : r < 0) (s : ℕ) :
    rankTwoPowCoeff P r s = if s = 0 then 1 else 0 := by
  simp [rankTwoPowCoeff, not_le.mpr hr]

/-- `π_{r,0}(P) = 1` when `P` has constant coefficient `1`. -/
@[simp]
theorem rankTwoPowCoeff_zero {P : S[X]} (hP : P.coeff 0 = 1) (r : ℤ) :
    rankTwoPowCoeff P r 0 = 1 := by
  rcases le_or_gt 0 r with hr | hr
  · rw [rankTwoPowCoeff_of_nonneg P hr, ← constantCoeff_apply, map_pow, constantCoeff_apply,
      hP, one_pow]
  · simp [rankTwoPowCoeff_of_neg P hr]

/-- `π_{d - q, s}(P)` is the coefficient of `z^s` in `P ^ (d - min d q)`: for `q > d` both are
`1` at `s = 0` and `0` otherwise. -/
theorem rankTwoPowCoeff_sub_eq_coeff_pow (P : S[X]) (d q s : ℕ) :
    rankTwoPowCoeff P ((d : ℤ) - q) s = (P ^ (d - min d q)).coeff s := by
  rcases le_or_gt q d with h | h
  · have h_toNat : ((d : ℤ) - q).toNat = d - q := by omega
    rw [rankTwoPowCoeff_of_nonneg P (by omega), min_eq_right h, h_toNat]
  · rw [rankTwoPowCoeff_of_neg P (by omega), min_eq_left h.le, Nat.sub_self, pow_zero, coeff_one]


end Polynomial

namespace Mei.RankTwo

variable {S : Type*} [Semiring S]
variable (d₁ d₂ : ℕ) (P₁ P₂ : S[X])

/-- The initial values, the recursion (R) and the vanishing conditions (V) for a pair of
coefficient families `C₊, C₋`. -/
structure IsRankTwoSolution (Cp Cm : ℕ → ℕ → S) : Prop where
  /-- `C₊(0, 0) = 1`. -/
  plus_zero_zero : Cp 0 0 = 1
  /-- `C₋(0, 0) = 1`. -/
  minus_zero_zero : Cm 0 0 = 1
  /-- The recursion (R). -/
  recursion : ∀ p q : ℕ,
    ∑ s ∈ range (p + 1), rankTwoPowCoeff P₁ ((d₂ : ℤ) - q) s * Cp (p - s) q =
      ∑ s ∈ range (q + 1), rankTwoPowCoeff P₂ ((d₁ : ℤ) - p) s * Cm p (q - s)
  /-- `C₊(p, q) = 0` off `(0, 0)` when `d₁ q ≤ d₂ p`. -/
  plus_eq_zero : ∀ p q : ℕ, (p, q) ≠ (0, 0) → d₁ * q ≤ d₂ * p → Cp p q = 0
  /-- `C₋(p, q) = 0` off `(0, 0)` when `d₂ p ≤ d₁ q`. -/
  minus_eq_zero : ∀ p q : ℕ, (p, q) ≠ (0, 0) → d₂ * p ≤ d₁ * q → Cm p q = 0

variable {d₁ d₂ P₁ P₂}

/-- The recursion with its new terms `C₊(p, q)` and `C₋(p, q)` separated. -/
private theorem IsRankTwoSolution.recursion_succ {Cp Cm : ℕ → ℕ → S}
    (h : IsRankTwoSolution d₁ d₂ P₁ P₂ Cp Cm) (hP₁ : P₁.coeff 0 = 1) (hP₂ : P₂.coeff 0 = 1)
    (p q : ℕ) :
    Cp p q + ∑ s ∈ range p, rankTwoPowCoeff P₁ ((d₂ : ℤ) - q) (s + 1) * Cp (p - (s + 1)) q =
      Cm p q + ∑ s ∈ range q, rankTwoPowCoeff P₂ ((d₁ : ℤ) - p) (s + 1) * Cm p (q - (s + 1)) := by
  have := h.recursion p q
  rw [sum_range_succ', sum_range_succ', rankTwoPowCoeff_zero hP₁, rankTwoPowCoeff_zero hP₂,
    one_mul, one_mul, Nat.sub_zero, Nat.sub_zero] at this
  rw [add_comm (Cp p q), add_comm (Cm p q)]
  exact this

/-- **Uniqueness.** When `P₁` and `P₂` have constant coefficient `1`, the initial values, (R)
and (V) determine `C₊` and `C₋`. -/
theorem IsRankTwoSolution.unique [IsCancelAdd S] {Cp Cm Cp' Cm' : ℕ → ℕ → S}
    (h : IsRankTwoSolution d₁ d₂ P₁ P₂ Cp Cm) (h' : IsRankTwoSolution d₁ d₂ P₁ P₂ Cp' Cm')
    (hP₁ : P₁.coeff 0 = 1) (hP₂ : P₂.coeff 0 = 1) : Cp = Cp' ∧ Cm = Cm' := by
  have key : ∀ n p q, p + q = n → Cp p q = Cp' p q ∧ Cm p q = Cm' p q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p q hpq
      by_cases h00 : (p, q) = (0, 0)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h00
        exact ⟨h.plus_zero_zero.trans h'.plus_zero_zero.symm,
          h.minus_zero_zero.trans h'.minus_zero_zero.symm⟩
      have hp : ∀ s ∈ range p, Cp (p - (s + 1)) q = Cp' (p - (s + 1)) q := fun s hs ↦
        (ih (p - (s + 1) + q) (by have := mem_range.mp hs; omega) _ _ rfl).1
      have hq : ∀ s ∈ range q, Cm p (q - (s + 1)) = Cm' p (q - (s + 1)) := fun s hs ↦
        (ih (p + (q - (s + 1))) (by have := mem_range.mp hs; omega) _ _ rfl).2
      have e := h.recursion_succ hP₁ hP₂ p q
      have e' := h'.recursion_succ hP₁ hP₂ p q
      have hsp : ∑ s ∈ range p, rankTwoPowCoeff P₁ ((d₂ : ℤ) - q) (s + 1) * Cp (p - (s + 1)) q =
          ∑ s ∈ range p, rankTwoPowCoeff P₁ ((d₂ : ℤ) - q) (s + 1) * Cp' (p - (s + 1)) q :=
        sum_congr rfl fun s hs ↦ by rw [hp s hs]
      have hsq : ∑ s ∈ range q, rankTwoPowCoeff P₂ ((d₁ : ℤ) - p) (s + 1) * Cm p (q - (s + 1)) =
          ∑ s ∈ range q, rankTwoPowCoeff P₂ ((d₁ : ℤ) - p) (s + 1) * Cm' p (q - (s + 1)) :=
        sum_congr rfl fun s hs ↦ by rw [hq s hs]
      rw [hsp, hsq] at e
      rcases le_or_gt (d₁ * q) (d₂ * p) with hle | hlt
      · have h₁ := h.plus_eq_zero p q h00 hle
        have h₁' := h'.plus_eq_zero p q h00 hle
        rw [h₁] at e
        rw [h₁'] at e'
        refine ⟨h₁.trans h₁'.symm, add_right_cancel (e.symm.trans e')⟩
      · have h₂ := h.minus_eq_zero p q h00 hlt.le
        have h₂' := h'.minus_eq_zero p q h00 hlt.le
        rw [h₂] at e
        rw [h₂'] at e'
        exact ⟨add_right_cancel (e.trans e'.symm), h₂.trans h₂'.symm⟩
  exact ⟨funext fun p ↦ funext fun q ↦ (key _ p q rfl).1,
    funext fun p ↦ funext fun q ↦ (key _ p q rfl).2⟩

end Mei.RankTwo
