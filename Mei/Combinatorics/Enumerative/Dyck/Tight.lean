/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Combinatorics.Enumerative.Dyck.Vanishing
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Shadowed and tight grading sums

For polynomials `P₁, P₂` and the maximal Dyck path of `(d₁, d₂)`, `shadowedSum p q` is the weight
sum of the shadowed gradings with totals `(p, q)`, and `tightSum p q` the weight sum of the tight
ones. With `p = k a` and `q = k b`, they are the right-hand sides of the rank-two power and
coefficient formulas of Burcroff–Lee–Mou (Theorem 5.17 and Remark 5.20), which express the
degree-`k(a, b)` coefficient of a power of a rank-two wall function, respectively of the wall
function itself, by these sums.

A shadowed grading is counted by `C₊ = cplus` or by `C₋ = cminus`, according to which of its
supports lies in the opposite total shadow. By the slope bounds behind the vanishing conditions
(V), a nonzero grading of the first kind has `d₂ p < d₁ q` and one of the second kind has
`d₁ q < d₂ p`, so the two kinds are disjoint and the shadowed sum reduces to `C₊` or `C₋`.

## Main statements

* `shadowedSum_eq_cplus_add_cminus`: off `(0, 0)`, the shadowed sum is `C₊(p, q) + C₋(p, q)`.
* `shadowedSum_eq_cplus`: if `d₂ p ≤ d₁ q`, the shadowed sum is `C₊(p, q)`;
  `shadowedSum_eq_cminus` is dual.
* `tightSum_eq_shadowedSum`, `tightSum_eq_zero`: the tight sum is the shadowed sum when
  `p ≤ d₁`, `q ≤ d₂` and `|p d₂ - q d₁| = gcd(p, q)`, and zero otherwise.
* `tightSum_mul_eq_cplus`: if `b d₁ - a d₂ = 1`, `k a ≤ d₁` and `k b ≤ d₂`, then
  `tightSum (k a) (k b) = C₊(k a, k b)`; `tightSum_mul_eq_cminus` treats `a d₂ - b d₁ = 1`.

## References

* Amanda Burcroff, Kyungyong Lee, Lang Mou, *Positivity of generalized cluster scattering
  diagrams*, Definitions 5.3–5.4, Theorem 5.17 and Remark 5.20, arXiv:2503.03719v1.
-/

public section

open Finset Polynomial

namespace Mei.MaximalDyckPath

variable {d₁ d₂ : ℕ} {S : Type*} [CommSemiring S] (P₁ P₂ : S[X])

variable (d₁ d₂) in
/-- The weight sum of the shadowed gradings with totals `(p, q)`. -/
def shadowedSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Shadowed γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem shadowedSum_def (p q : ℕ) :
    shadowedSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Shadowed γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

variable (d₁ d₂) in
/-- The weight sum of the tight gradings with totals `(p, q)`. -/
def tightSum (p q : ℕ) : S :=
  ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Tight γ ∧ verticalTotal γ = p ∧
    horizontalTotal γ = q, weight P₁ P₂ γ

theorem tightSum_def (p q : ℕ) :
    tightSum d₁ d₂ P₁ P₂ p q =
      ∑ γ ∈ gradings d₁ d₂ P₁.natDegree P₂.natDegree with Tight γ ∧ verticalTotal γ = p ∧
        horizontalTotal γ = q, weight P₁ P₂ γ :=
  (rfl)

/-- Off `(0, 0)`, the shadowed sum is `C₊(p, q) + C₋(p, q)`: a nonzero shadowed grading is
counted by exactly one of `C₊` and `C₋`. -/
theorem shadowedSum_eq_cplus_add_cminus {p q : ℕ} (h0 : (p, q) ≠ (0, 0)) :
    shadowedSum d₁ d₂ P₁ P₂ p q = cplus d₁ d₂ P₁ P₂ p q + cminus d₁ d₂ P₁ P₂ p q := by
  rw [shadowedSum_def, cplus_def, cminus_def, ← sum_union]
  · refine sum_congr ?_ fun _ _ ↦ rfl
    ext γ
    simp only [mem_union, mem_filter, shadowed_iff]
    tauto
  · rw [disjoint_filter]
    rintro γ - ⟨hc, rfl, rfl, hs⟩ ⟨-, -, -, hs'⟩
    have hγ : γ ≠ 0 := fun hγ ↦ h0 (by rw [hγ, verticalTotal_zero, horizontalTotal_zero])
    exact lt_asymm (mul_verticalTotal_lt_mul_horizontalTotal hc hs hγ)
      (mul_horizontalTotal_lt_mul_verticalTotal hc hs' hγ)

/-- If `d₂ p ≤ d₁ q`, the shadowed sum is `C₊(p, q)`: no nonzero grading counted by `C₋` has
these totals. -/
theorem shadowedSum_eq_cplus {p q : ℕ} (hpq : d₂ * p ≤ d₁ * q) :
    shadowedSum d₁ d₂ P₁ P₂ p q = cplus d₁ d₂ P₁ P₂ p q := by
  rw [shadowedSum_def, cplus_def]
  refine sum_congr (filter_congr fun γ _ ↦ ?_) fun _ _ ↦ rfl
  rw [shadowed_iff]
  constructor
  · rintro ⟨⟨hc, hs | hs⟩, rfl, rfl⟩
    · refine ⟨hc, rfl, rfl, ?_⟩
      rcases eq_or_ne γ 0 with rfl | hγ
      · simp
      · exact absurd hpq (mul_horizontalTotal_lt_mul_verticalTotal hc hs hγ).not_ge
    · exact ⟨hc, rfl, rfl, hs⟩
  · rintro ⟨hc, hp, hq, hs⟩
    exact ⟨⟨hc, Or.inr hs⟩, hp, hq⟩

/-- If `d₁ q ≤ d₂ p`, the shadowed sum is `C₋(p, q)`: no nonzero grading counted by `C₊` has
these totals. -/
theorem shadowedSum_eq_cminus {p q : ℕ} (hpq : d₁ * q ≤ d₂ * p) :
    shadowedSum d₁ d₂ P₁ P₂ p q = cminus d₁ d₂ P₁ P₂ p q := by
  rw [shadowedSum_def, cminus_def]
  refine sum_congr (filter_congr fun γ _ ↦ ?_) fun _ _ ↦ rfl
  rw [shadowed_iff]
  constructor
  · rintro ⟨⟨hc, hs | hs⟩, rfl, rfl⟩
    · exact ⟨hc, rfl, rfl, hs⟩
    · refine ⟨hc, rfl, rfl, ?_⟩
      rcases eq_or_ne γ 0 with rfl | hγ
      · simp
      · exact absurd hpq (mul_verticalTotal_lt_mul_horizontalTotal hc hs hγ).not_ge
  · rintro ⟨hc, hp, hq, hs⟩
    exact ⟨⟨hc, Or.inl hs⟩, hp, hq⟩

/-- The shadowed sum at `(0, 0)` is `1` when both constant coefficients are one. -/
@[simp]
theorem shadowedSum_zero_zero (h₁ : P₁.coeff 0 = 1) (h₂ : P₂.coeff 0 = 1) :
    shadowedSum d₁ d₂ P₁ P₂ 0 0 = 1 := by
  rw [shadowedSum_eq_cplus P₁ P₂ (by simp), cplus_zero_zero P₁ P₂ h₁ h₂]

/-- The tight sum is the shadowed sum when `p ≤ d₁`, `q ≤ d₂` and `|p d₂ - q d₁| = gcd(p, q)`. -/
theorem tightSum_eq_shadowedSum {p q : ℕ} (hp : p ≤ d₁) (hq : q ≤ d₂)
    (hpq : ((p * d₂ : ℤ) - q * d₁).natAbs = p.gcd q) :
    tightSum d₁ d₂ P₁ P₂ p q = shadowedSum d₁ d₂ P₁ P₂ p q := by
  rw [tightSum_def, shadowedSum_def]
  refine sum_congr (filter_congr fun γ _ ↦ ?_) fun _ _ ↦ rfl
  rw [tight_iff]
  constructor
  · exact fun ⟨⟨hs, _⟩, hγ⟩ ↦ ⟨hs, hγ⟩
  · rintro ⟨hs, rfl, rfl⟩
    exact ⟨⟨hs, hp, hq, hpq⟩, rfl, rfl⟩

/-- The tight sum vanishes unless `p ≤ d₁`, `q ≤ d₂` and `|p d₂ - q d₁| = gcd(p, q)`. -/
theorem tightSum_eq_zero {p q : ℕ}
    (h : ¬(p ≤ d₁ ∧ q ≤ d₂ ∧ ((p * d₂ : ℤ) - q * d₁).natAbs = p.gcd q)) :
    tightSum d₁ d₂ P₁ P₂ p q = 0 := by
  rw [tightSum_def]
  refine sum_eq_zero fun γ hγ ↦ absurd hγ ?_
  rw [mem_filter, tight_iff]
  rintro ⟨-, ⟨-, hp, hq, hpq⟩, rfl, rfl⟩
  exact h ⟨hp, hq, hpq⟩

/-- **Tight sums as `C₊`.** If `b d₁ - a d₂ = 1`, `k a ≤ d₁` and `k b ≤ d₂`, then the tight sum
with totals `(k a, k b)` is `C₊(k a, k b)`. -/
theorem tightSum_mul_eq_cplus {a b k : ℕ} (hab : (b * d₁ : ℤ) - a * d₂ = 1) (ha : k * a ≤ d₁)
    (hb : k * b ≤ d₂) :
    tightSum d₁ d₂ P₁ P₂ (k * a) (k * b) = cplus d₁ d₂ P₁ P₂ (k * a) (k * b) := by
  have hcop : a.Coprime b := Nat.isCoprime_iff_coprime.mp ⟨-d₂, d₁, by linear_combination hab⟩
  rw [tightSum_eq_shadowedSum P₁ P₂ ha hb, shadowedSum_eq_cplus]
  · have : (d₂ * (k * a) : ℤ) ≤ d₁ * (k * b) := by nlinarith
    exact_mod_cast this
  · rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    have : ((k * a : ℕ) * d₂ : ℤ) - (k * b : ℕ) * d₁ = -k := by
      push_cast
      linear_combination (-(k : ℤ)) * hab
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]

/-- **Tight sums as `C₋`.** If `a d₂ - b d₁ = 1`, `k a ≤ d₁` and `k b ≤ d₂`, then the tight sum
with totals `(k a, k b)` is `C₋(k a, k b)`. -/
theorem tightSum_mul_eq_cminus {a b k : ℕ} (hab : (a * d₂ : ℤ) - b * d₁ = 1) (ha : k * a ≤ d₁)
    (hb : k * b ≤ d₂) :
    tightSum d₁ d₂ P₁ P₂ (k * a) (k * b) = cminus d₁ d₂ P₁ P₂ (k * a) (k * b) := by
  have hcop : a.Coprime b := Nat.isCoprime_iff_coprime.mp ⟨d₂, -d₁, by linear_combination hab⟩
  rw [tightSum_eq_shadowedSum P₁ P₂ ha hb, shadowedSum_eq_cminus]
  · have : (d₁ * (k * b) : ℤ) ≤ d₂ * (k * a) := by nlinarith
    exact_mod_cast this
  · rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    have : ((k * a : ℕ) * d₂ : ℤ) - (k * b : ℕ) * d₁ = k := by
      push_cast
      linear_combination (k : ℤ) * hab
    rw [this, Int.natAbs_natCast]

end Mei.MaximalDyckPath
