/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Skew.Radical
public import Mei.Geometry.ScatteringDiagram.Skew.Comparison.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.LieAlgebra

/-!
# Radical degrees of a skew lattice datum

A vector `n` lies in the radical of the skew form `{,}` when `{-, n} = 0`
(`SkewLatticeDatum.form_flip_eq_zero_iff` identifies it with `{n, -} = 0`). For an unfrozen
radical `n`:

* The normal `{-, κ(n) n}` is zero (`SkewLatticeDatum.normal_eq_zero_iff`), and so is its
  comparison counterpart: evaluation at `n` pulled back along the skew comparison
  `x ↦ {x, -}` vanishes (`SkewLatticeDatum.eval_comp_skewComparison_eq_zero_iff`).
* In the positive skew Lie algebra, brackets of total degree `n` vanish
  (`SkewLatticeDatum.lie_eq_zero_of_form_flip_add_eq_zero`), and the Poisson action of `X_n`
  on monomials is zero (`SkewLatticeDatum.action_single_eq_zero_of_form_flip_eq_zero`). For the
  zero form the whole Poisson action vanishes (`SkewLatticeDatum.action_eq_zero_of_form_eq_zero`).

The principal counterparts are stated with the principal data: `p₁*(n) = 0` exactly for
radical `n` (`SkewLatticeDatum.principalCharacter_eq_zero_iff`), and projected principal walls
of radical degree have zero velocity and are incoming
(`SkewLatticeDatum.projectedPrincipal_direction_eq_zero_of_form_flip_eq_zero`,
`SkewLatticeDatum.incoming_of_form_flip_eq_zero`).
Conventions follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1
and Appendix B (arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] (D : SkewLatticeDatum N)

/-- The right and left radicals of a skew form agree. -/
theorem form_flip_eq_zero_iff {n : N} : D.form.flip n = 0 ↔ D.form n = 0 := by
  constructor <;> intro hn <;> ext a
  · simpa [D.form_swap n a] using LinearMap.congr_fun hn a
  · simpa [D.form_swap a n] using LinearMap.congr_fun hn a

/-- The normal `{-, κ(n) n}` of an unfrozen vector vanishes exactly when the vector lies in the
radical of the form. -/
theorem normal_eq_zero_iff [Module.Free ℤ N] {n : N} (hn : n ∈ D.unfrozen) :
    D.normal n hn = 0 ↔ D.form.flip n = 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    simpa only [map_zero, iff_true] using D.normal_zero
  have hκ : (D.sublattice.toAddSubgroup.rayIndex n : ℚ) ≠ 0 :=
    (D.sublattice.toAddSubgroup.rayIndex_pos hn0).ne'
  constructor
  · intro h
    ext a
    have he := D.cast_normal_apply hn a
    rw [h, LinearMap.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at he
    simpa using he.resolve_left hκ
  · intro h
    ext a
    apply Int.cast_injective (α := ℚ)
    rw [D.cast_normal_apply hn a]
    simpa using Or.inr (LinearMap.congr_fun h a)

section Lie

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- A radical unfrozen degree is in the radical of the coefficient form. -/
theorem coefficientForm_flip_eq_zero {n : D.unfrozen} (hn : D.form.flip n = 0) :
    (D.coefficientForm R).flip n = 0 := by
  ext a
  have ha := LinearMap.congr_fun hn a
  rw [LinearMap.flip_apply, LinearMap.zero_apply] at ha
  simp [ha]

/-- In the positive skew Lie algebra, homogeneous elements whose degrees add up to a radical
degree commute. -/
theorem lie_eq_zero_of_form_flip_add_eq_zero (d : PositiveDegrees D.unfrozen)
    {a b : D.unfrozen} (hab : D.form.flip ((a + b : D.unfrozen) : N) = 0)
    {x y : SkewLieAlgebra.positiveLieAlgebra (D.coefficientForm R)
      (D.isAlt_coefficientForm R) d}
    (hx : x ∈ SkewLieAlgebra.positiveGrading _ (D.isAlt_coefficientForm R) d a)
    (hy : y ∈ SkewLieAlgebra.positiveGrading _ (D.isAlt_coefficientForm R) d b) :
    ⁅x, y⁆ = 0 :=
  SkewLieAlgebra.positiveGrading_lie_eq_zero_of_flip_add_eq_zero _ _ d
    (D.coefficientForm_flip_eq_zero R hab) hx hy

/-- A generator of radical degree acts by zero in the Poisson action. -/
theorem action_single_eq_zero_of_form_flip_eq_zero {n : D.unfrozen}
    (hn : D.form.flip n = 0) (r : R) :
    SkewLieAlgebra.action _ (D.isAlt_coefficientForm R)
      (SkewLieAlgebra.single _ (D.isAlt_coefficientForm R) n r) = 0 :=
  SkewLieAlgebra.action_single_eq_zero_of_flip_eq_zero _ _ (D.coefficientForm_flip_eq_zero R hn) r

/-- The zero form has the trivial Poisson action. -/
theorem action_eq_zero_of_form_eq_zero (hform : D.form = 0) :
    SkewLieAlgebra.action _ (D.isAlt_coefficientForm R) = 0 := by
  apply SkewLieAlgebra.action_eq_zero_of_eq_zero
  ext a b
  simp [hform]

end Lie

section Comparison

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (hD : ∀ a b, ∃ k : ℤ, D.form a b = k)
  {i : N →+ V} (h : TauCeti.Toric.IsIntegralLattice i)

/-- Evaluation at a lattice vector pulls back to zero along the skew comparison exactly when
the vector lies in the radical of the form. -/
theorem eval_comp_skewComparison_eq_zero_iff (n : N) :
    ((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap).comp (D.skewComparison hD h) = 0 ↔
      D.form.flip n = 0 := by
  rw [D.eval_comp_skewComparison hD h n, ← map_zero h.realCharacter,
    h.realCharacter_injective.eq_iff]
  constructor <;> intro hn <;> ext a
  · have he := congrArg (Int.cast (R := ℚ)) (DFunLike.congr_fun hn a)
    simpa [D.cast_integralCharacter_apply hD] using he
  · apply Int.cast_injective (α := ℚ)
    simpa [D.cast_integralCharacter_apply hD] using LinearMap.congr_fun hn a

end Comparison

end Mei.SkewLatticeDatum
