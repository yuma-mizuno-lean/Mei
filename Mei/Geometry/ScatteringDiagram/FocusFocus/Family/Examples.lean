/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family.Opposite

/-!
# Broken lines of the common focus-focus family at `(1, 1)`

The incoming monomial `X^d = ϑ_{-d, 0}`, `d > 0`, comes from the left chamber. At the endpoint
`Q = (1, 1)` of the right chamber every crossing height `1 + j / d` is positive, so by
`slabThetaFamilyOppositeFiberEquiv` the broken lines of the common family `slabThetaFamily`
ending at `Q` are the upper crossing charts of the indices `j ≤ d` with `t^d binom(d, j) ≠ 0`,
with weights `t^d binom(d, j) z^{(-d, j)}` (`slabThetaFamilyFiberOneOneEquiv`).

* `exists_slabThetaFamily_fiber_one_one_neg_one`: if `t ≠ 0`, the monomial `X` has two broken
  lines at `Q`, with weights `t z^{(-1, 0)}` and `t z^{(-1, 1)}`.
* `exists_slabThetaFamily_fiber_one_one_neg_two`: if `2 t² ≠ 0`, the monomial `X²` has three
  broken lines at `Q`, with weights `t² z^{(-2, 0)}`, `2 t² z^{(-2, 1)}` and `t² z^{(-2, 2)}`.
* `card_slabThetaFamily_fiber_one_one_truncated`: over `ℤ[t]/(t³)`, the smoothing ring of order
  `k = 2` over `K = ℤ`, these are two and three broken lines, with binomial weights `1, 1` and
  `1, 2, 1`.
* `card_slabThetaFamily_fiber_one_one_neg_two_zmod_two`: over `ZMod 2` with `t = 1`, the middle
  decoration `2 t² z^{(-2, 1)}` vanishes and its broken line is discarded, leaving two lines for
  `X²`.

This is the broken-line count of the focus-focus example of Gross–Siebert, *An Invitation to
Toric Degenerations*, §2.3 (arXiv:0808.2749v2), read off the common family.
-/

public noncomputable section

open AddMonoidAlgebra

namespace Mei.FocusFocus

variable {R : Type*} [CommRing R] (t : R)
  (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- For a monomial from the left chamber, every crossing height at `(1, 1)` is positive. -/
theorem crossingHeight_one_one_pos {n : ℤ} (hn : n < 0) (j : ℕ) :
    0 < ((1, 1) : ℝ × ℝ).2 - (((0 : ℤ) + j : ℤ) : ℝ) * ((1, 1) : ℝ × ℝ).1 / n := by
  have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
  have hj : (j : ℝ) / n ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨j.cast_nonneg, hn'.le⟩)
  push_cast
  rw [zero_add, mul_one]
  linarith

/-- The endpoint `(1, 1)` lies in the chamber opposite to a monomial from the left. -/
theorem one_one_div_neg {n : ℤ} (hn : n < 0) : ((1, 1) : ℝ × ℝ).1 / (n : ℝ) < 0 :=
  div_neg_of_pos_of_neg one_pos (by exact_mod_cast hn)

/-- If every binomial decoration of a monomial `X^{|n|}` from the left survives, its broken lines
of the common family at `(1, 1)` are indexed by all binomial indices `j ≤ |n|`. -/
def slabThetaFamilyFiberOneOneEquiv {n : ℤ} (hn : n < 0)
    (ht : ∀ j : Fin (n.natAbs + 1), t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0) :
    (slabThetaFamily t 1 n 0 h).fiber (1, 1) ≃ Fin (n.natAbs + 1) :=
  (slabThetaFamilyOppositeFiberEquiv t 1 n 0 h (one_one_div_neg hn)).trans
    (Equiv.subtypeUnivEquiv fun j =>
      ⟨by simpa only [one_mul] using ht j, (crossingHeight_one_one_pos hn j.val).ne'⟩)

/-- The broken line of the binomial index `j` at `(1, 1)` has weight
`t^{|n|} binom(|n|, j) z^{(-|n|, j)}`. -/
theorem slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm {n : ℤ} (hn : n < 0)
    (ht : ∀ j : Fin (n.natAbs + 1), t ^ n.natAbs * (n.natAbs.choose j.val : R) ≠ 0)
    (j : Fin (n.natAbs + 1)) :
    slabThetaChartWeight t 1 n 0 ((slabThetaFamilyFiberOneOneEquiv t h hn ht).symm j).1 =
      single (-(n.natAbs : ℤ), (j.val : ℤ)) (t ^ n.natAbs * (n.natAbs.choose j.val : R)) := by
  rw [slabThetaChartWeight_of_opposite t 1 n 0 h (one_one_div_neg hn)]
  simp [slabThetaFamilyFiberOneOneEquiv]

/-- If `t ≠ 0`, the incoming monomial `X = ϑ_{-1, 0}` from the left has exactly two
broken lines ending at `(1, 1)`, with weights `t z^{(-1, 0)}` and `t z^{(-1, 1)}`. -/
theorem exists_slabThetaFamily_fiber_one_one_neg_one (ht : t ≠ 0) :
    ∃ e : Fin 2 ≃ (slabThetaFamily t 1 (-1) 0 h).fiber (1, 1),
      slabThetaChartWeight t 1 (-1) 0 (e 0).1 = single (-1, 0) t ∧
        slabThetaChartWeight t 1 (-1) 0 (e 1).1 = single (-1, 1) t := by
  have hall : ∀ j : Fin ((-1 : ℤ).natAbs + 1),
      t ^ (-1 : ℤ).natAbs * ((-1 : ℤ).natAbs.choose j.val : R) ≠ 0 := by
    intro j
    fin_cases j <;> simpa using ht
  refine ⟨(slabThetaFamilyFiberOneOneEquiv t h (by norm_num) hall).symm, ?_, ?_⟩
  · simpa using slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm t h
      (by norm_num) hall 0
  · simpa using slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm t h
      (by norm_num) hall 1

/-- If `2 t² ≠ 0`, the incoming monomial `X² = ϑ_{-2, 0}` from the left has exactly
three broken lines ending at `(1, 1)`, with weights `t² z^{(-2, 0)}`, `2 t² z^{(-2, 1)}` and
`t² z^{(-2, 2)}`. -/
theorem exists_slabThetaFamily_fiber_one_one_neg_two (ht : (2 : R) * t ^ 2 ≠ 0) :
    ∃ e : Fin 3 ≃ (slabThetaFamily t 1 (-2) 0 h).fiber (1, 1),
      slabThetaChartWeight t 1 (-2) 0 (e 0).1 = single (-2, 0) (t ^ 2) ∧
        slabThetaChartWeight t 1 (-2) 0 (e 1).1 = single (-2, 1) (2 * t ^ 2) ∧
          slabThetaChartWeight t 1 (-2) 0 (e 2).1 = single (-2, 2) (t ^ 2) := by
  have ht' : t ^ 2 ≠ 0 := fun h0 => ht (by rw [h0, mul_zero])
  have hall : ∀ j : Fin ((-2 : ℤ).natAbs + 1),
      t ^ (-2 : ℤ).natAbs * ((-2 : ℤ).natAbs.choose j.val : R) ≠ 0 := by
    intro j
    fin_cases j
    · simpa using ht'
    · simpa [mul_comm] using ht
    · simpa using ht'
  refine ⟨(slabThetaFamilyFiberOneOneEquiv t h (by norm_num) hall).symm, ?_, ?_, ?_⟩
  · simpa using slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm t h
      (by norm_num) hall 0
  · simpa [mul_comm] using slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm t h
      (by norm_num) hall 1
  · simpa using slabThetaChartWeight_slabThetaFamilyFiberOneOneEquiv_symm t h
      (by norm_num) hall 2

open Polynomial in
/-- Over the smoothing ring `ℤ[t]/(t³)` of order `k = 2`, the incoming monomials `X`
and `X²` from the left have respectively two and three broken lines ending at `(1, 1)`. -/
theorem card_slabThetaFamily_fiber_one_one_truncated :
    Nat.card ((slabThetaFamily (Ideal.Quotient.mk (Ideal.span {(X : ℤ[X]) ^ 3}) X) 1 (-1) 0
        h).fiber (1, 1)) = 2 ∧
      Nat.card ((slabThetaFamily (Ideal.Quotient.mk (Ideal.span {(X : ℤ[X]) ^ 3}) X) 1 (-2) 0
        h).fiber (1, 1)) = 3 := by
  -- A nonzero multiple of `t^d` survives in `ℤ[t]/(t³)` for `d ≤ 2`.
  have key (m d : ℕ) (hd : d ≤ 2) (hm : m ≠ 0) :
      (m : ℤ[X] ⧸ Ideal.span {(X : ℤ[X]) ^ 3}) *
        Ideal.Quotient.mk (Ideal.span {(X : ℤ[X]) ^ 3}) X ^ d ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ne,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_iff]
    intro hall
    have hcoeff := hall d (by omega)
    rw [← C_eq_natCast, coeff_C_mul_X_pow] at hcoeff
    simp only [↓reduceIte, Int.natCast_eq_zero] at hcoeff
    exact hm hcoeff
  obtain ⟨e₁, -⟩ := exists_slabThetaFamily_fiber_one_one_neg_one
    (Ideal.Quotient.mk (Ideal.span {(X : ℤ[X]) ^ 3}) X) h
    (by simpa using key 1 1 (by norm_num) one_ne_zero)
  obtain ⟨e₂, -⟩ := exists_slabThetaFamily_fiber_one_one_neg_two
    (Ideal.Quotient.mk (Ideal.span {(X : ℤ[X]) ^ 3}) X) h
    (by simpa using key 2 2 le_rfl two_ne_zero)
  exact ⟨(Nat.card_congr e₁.symm).trans (Nat.card_fin 2),
    (Nat.card_congr e₂.symm).trans (Nat.card_fin 3)⟩

/-- Over `ZMod 2` with `t = 1`, the middle decoration `2 t² z^{(-2, 1)}` of `X²` vanishes, so its
broken line is discarded and only two broken lines end at `(1, 1)`. -/
theorem card_slabThetaFamily_fiber_one_one_neg_two_zmod_two :
    Nat.card ((slabThetaFamily (1 : ZMod 2) 1 (-2) 0 h).fiber (1, 1)) = 2 := by
  -- Every crossing height is nonzero, so only the binomial decorations select branches.
  let e : SlabBranchIndex (1 : ZMod 2) 1 (-2) 0 (1, 1) ≃
      {j : Fin ((-2 : ℤ).natAbs + 1) //
        (1 : ZMod 2) * 1 ^ (-2 : ℤ).natAbs * ((-2 : ℤ).natAbs.choose j.val : ZMod 2) ≠ 0} :=
    Equiv.subtypeEquivRight fun j =>
      and_iff_left (crossingHeight_one_one_pos (by norm_num) j.val).ne'
  rw [card_slabThetaFamily_fiber_of_opposite _ _ _ _ h (one_one_div_neg (by norm_num)),
    Nat.card_congr e, Nat.card_eq_fintype_card]
  simp only [one_mul, one_pow]
  decide

end Mei.FocusFocus
