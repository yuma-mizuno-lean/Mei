/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.MonoidAlgebra.Filtration.PowerSeries
public import Mei.RingTheory.FilteredAlgebra.Positive.InvOneSubPow
public import Mei.RingTheory.PowerSeries.InvOneSubPow

/-!
# A positive wall function that is not a polynomial

Take the standard orthant `ℕ²` of `ℤ²` with the coordinate-sum degree
(`TauCeti.PositiveDegrees.orthant (Fin 2)`), with its own monoid as coefficient monoid. Wall
functions are then units of the completion of `ℚ[x, y]` for the positive-increment filtration
`Mei.TropicalVertexCoefficientAction.filtration`. Write `x²y²` for the monomial of exponent
`(2, 2)` (`Mei.TropicalVertexCoefficientAction.Examples.diagonalExponent`). The unit
`(1 - x²y²)⁻²` (`Mei.TropicalVertexCoefficientAction.Examples.badlandsWallFunction`):

* is the series `∑_{k ≥ 0} (k + 1) x^{2k} y^{2k}`: its order-`k` projection is the class of the
  partial sum up to `k`
  (`Mei.TropicalVertexCoefficientAction.Examples.projection_badlandsWallFunction`), and its
  inverse is `(1 - x²y²)²`
  (`Mei.TropicalVertexCoefficientAction.Examples.val_inv_badlandsWallFunction`);
* is positive for the image of `ℕ[x, y]`
  (`Mei.TropicalVertexCoefficientAction.Examples.isPositive_badlandsWallFunction`), the notion
  required of grouped wall functions by `Mei.DirectedDiagram.FunctionWallGrouping.IsPositive`;
* is not the completion of any element of `ℚ[x, y]`
  (`Mei.TropicalVertexCoefficientAction.Examples.badlandsWallFunction_notMem_range_toCompletion`).

So positivity in the sense of `TauCeti.AlgFiltration.IsPositive`, a condition on finite-order
projections, holds here for a unit that is not the completion of a polynomial. By contrast, the
incoming wall functions of a rank-two polynomial input are completions of polynomials
(`Mei.RankTwoPolynomialInput.coe_completedInitialFunction`).

By Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Example 5.21
(arXiv:2503.03719v1), this series is the wall function on the ray `ℝ_{≤0}(1, 1)` of the cluster
scattering diagram of affine type `(2, 2)`, with incoming wall functions `1 + x²` and `1 + y²`.
That identification needs the consistent completion of this diagram, and is not formalized
here; only the properties of the series listed above are.
-/

public section

open TauCeti (AlgFiltration)

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.TropicalVertexCoefficientAction.Examples

open _root_.AddMonoidAlgebra TauCeti.PositiveDegrees

local notation "Q" => PositiveDegrees.monoid (orthant (Fin 2))
local notation "F" => filtration (R := ℚ) (orthant (Fin 2)) Q
local notation "𝒫" => RingHom.rangeS (mapRingHom Q (Nat.castRingHom ℚ))

/-- The exponent `(2, 2)` of the standard orthant of `ℤ²`. -/
def diagonalExponent : Q := ⟨![2, 2], by simp [Fin.forall_fin_two]⟩

/-- The exponent `(2, 2)` is the vector `(2, 2)`. -/
@[simp]
theorem coe_diagonalExponent : (diagonalExponent : Fin 2 → ℤ) = ![2, 2] := (rfl)

/-- The exponent `(2, 2)` has coordinate-sum degree `4`. -/
theorem degree_diagonalExponent : (orthant (Fin 2)).degree diagonalExponent = 4 := by
  simp [Fin.sum_univ_two]

/-- The monomial `x²y²` lies in the first term of the positive-increment filtration. -/
theorem single_diagonalExponent_mem_filtration_ideal_one :
    single diagonalExponent (1 : ℚ) ∈ (F).ideal 1 := by
  rw [filtration_ideal, AddSubmonoid.single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨diagonalExponent, by simp, by simp, 0, (zero_add _).symm⟩

/-- The completed monomial `x²y²`, in the first completed ideal. -/
def diagonalMonomial : (F).completionIdeal 1 :=
  ⟨(F).toCompletion (single diagonalExponent 1),
    ((F).toCompletion_mem_completionIdeal_iff 1 _).mpr
      single_diagonalExponent_mem_filtration_ideal_one⟩

/-- The completed monomial `x²y²` is the completion of `x²y²`. -/
@[simp]
theorem coe_diagonalMonomial :
    (diagonalMonomial : (F).completion) = (F).toCompletion (single diagonalExponent 1) := (rfl)

/-- The wall function `(1 - x²y²)⁻² = ∑_{k ≥ 0} (k + 1) x^{2k} y^{2k}`, the evaluation of the
inverse of `(1 - X)²` at `x²y²`. -/
def badlandsWallFunction : (F).completionˣ :=
  Units.map ((F).completedAeval (R := ℚ) diagonalMonomial : PowerSeries ℚ →* (F).completion)
    (PowerSeries.invOneSubPow ℚ 2)

/-- The wall function is the inverse of `(1 - X)²` evaluated at `x²y²`. -/
@[simp]
theorem val_badlandsWallFunction :
    (badlandsWallFunction : (F).completion) =
      (F).completedAeval diagonalMonomial (PowerSeries.invOneSubPow ℚ 2 : PowerSeries ℚ) :=
  (rfl)

/-- The inverse of the wall function is `(1 - x²y²)²`. -/
@[simp]
theorem val_inv_badlandsWallFunction :
    ((badlandsWallFunction⁻¹ : (F).completionˣ) : (F).completion) =
      (1 - (F).toCompletion (single diagonalExponent 1)) ^ 2 := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [val_badlandsWallFunction, ← coe_diagonalMonomial]
  exact (F).completedAeval_invOneSubPow_mul_one_sub_pow diagonalMonomial 2

/-- At order `k`, the wall function is the class of `∑_{j ≤ k} (j + 1) x^{2j} y^{2j}`. -/
theorem projection_badlandsWallFunction (k : ℕ) :
    (F).projection k badlandsWallFunction =
      Ideal.Quotient.mk _
        (∑ j ∈ Finset.range (k + 1), single (j • diagonalExponent) ((j : ℚ) + 1)) := by
  rw [val_badlandsWallFunction,
    AlgFiltration.projection_completedAeval_of_val_eq_toCompletion_single coe_diagonalMonomial,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp [add_comm]

/-- The wall function `(1 - x²y²)⁻²` is positive for the image of `ℕ[x, y]`. -/
theorem isPositive_badlandsWallFunction : (F).IsPositive 𝒫 badlandsWallFunction := by
  rw [val_badlandsWallFunction]
  refine AlgFiltration.IsPositive.completedAeval_invOneSubPow ?_ 2
  rw [coe_diagonalMonomial]
  exact AlgFiltration.isPositive_toCompletion ⟨single diagonalExponent 1, by simp⟩

/-- The wall function `(1 - x²y²)⁻²` is not the completion of an element of `ℚ[x, y]`. -/
theorem badlandsWallFunction_notMem_range_toCompletion :
    (badlandsWallFunction : (F).completion) ∉ Set.range (F).toCompletion := by
  have hδ (n : Q) : 0 ≤ ((orthant (Fin 2)).degree.comp (Q).subtype) n :=
    (orthant (Fin 2)).degree_nonneg n.2
  have hm : 0 < ((orthant (Fin 2)).degree.comp (Q).subtype) diagonalExponent := by
    rw [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, degree_diagonalExponent]
    norm_num
  rw [val_badlandsWallFunction, AlgFiltration.completedAeval_mem_range_toCompletion_iff
    (fun k => (filtration_ideal (orthant (Fin 2)) Q k).le) hδ hm coe_diagonalMonomial]
  rintro ⟨p, hp⟩
  exact p.coe_ne_invOneSubPow two_ne_zero hp

end Mei.TropicalVertexCoefficientAction.Examples
