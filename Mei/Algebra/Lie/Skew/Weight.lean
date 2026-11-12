/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Skew.Ray
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Monomial weights of skew Lie algebras

A function `χ` on the exponent group defines the linear map `X_n ↦ χ(n) X_n` of a skew Lie
algebra (`SkewLieAlgebra.weightMap`). If `χ` is multiplicative on the monoid of positive
degree data, `χ(n + m) = χ(n) χ(m)` for allowed `n, m`, this map preserves the brackets of the
positive skew algebra and is a graded Lie endomorphism of fixed degree
(`SkewLieAlgebra.weightGradedLieHom`). The weight need not be a unit; for instance it may send
the basis vectors of an orthant to independent polynomial variables.

Its completed map rescales the variable of every ray label: the label
`exp(∑_{j ≥ 1} f_j X_{jn})` of a power series `f` goes to the label of `f(χ(n) T)`
(`SkewLieAlgebra.completedMap_weightGradedLieHom_rayExp`). Thus identities between ray labels
with coefficient one transport to identities between ray labels with monomial coefficients.

The construction parallels `SkewLieAlgebra.coefficientGradedLieHom`; Mathlib's
`PowerSeries.rescale` gives the rescaled series. Such weights are the coefficient variables of
the principal realization of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1 and Appendix B (arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) (χ : Γ → R)

/-- The weight map `X_n ↦ χ(n) X_n` of a skew Lie algebra, for an arbitrary function `χ` on the
exponent group. -/
def weightMap : SkewLieAlgebra β hβ →ₗ[R] SkewLieAlgebra β hβ :=
  (Finsupp.lsum R fun n => χ n • single β hβ n).comp (toFinsupp β hβ).toLinearMap

/-- The weight map multiplies a homogeneous generator by its weight. -/
@[simp]
theorem weightMap_single (n : Γ) (r : R) :
    weightMap β hβ χ (single β hβ n r) = single β hβ n (χ n * r) := by
  rw [weightMap, LinearMap.comp_apply, LinearEquiv.coe_coe, toFinsupp_single,
    Finsupp.lsum_single, LinearMap.smul_apply, ← map_smul, smul_eq_mul]

/-- The weight map multiplies each coefficient by its weight. -/
@[simp]
theorem toFinsupp_weightMap (x : SkewLieAlgebra β hβ) (n : Γ) :
    toFinsupp β hβ (weightMap β hβ χ x) n = χ n * toFinsupp β hβ x n := by
  classical
  induction x using induction_on β hβ with
  | h0 => simp
  | hs m r =>
    rw [weightMap_single, toFinsupp_single, toFinsupp_single, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | ha x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

/-- A skew Lie element is the sum of its homogeneous components over its support. -/
theorem sum_single_toFinsupp (x : SkewLieAlgebra β hβ) :
    ∑ n ∈ (toFinsupp β hβ x).support, single β hβ n (toFinsupp β hβ x n) = x := by
  apply (toFinsupp β hβ).injective
  rw [map_sum]
  simp only [toFinsupp_single]
  exact Finsupp.sum_single (toFinsupp β hβ x)

variable {d : PositiveDegrees Γ}

/-- The weight map preserves positive support. -/
theorem weightMap_mem_positiveLieAlgebra {x : SkewLieAlgebra β hβ}
    (hx : x ∈ positiveLieAlgebra β hβ d) : weightMap β hβ χ x ∈ positiveLieAlgebra β hβ d := by
  rw [mem_positiveLieAlgebra_iff] at hx ⊢
  intro n hn
  rw [toFinsupp_weightMap, hx n hn, mul_zero]

variable {χ} (hχ : ∀ n ∈ d.monoid, ∀ m ∈ d.monoid, χ (n + m) = χ n * χ m)
include hχ

/-- A weight multiplicative on the allowed monoid makes the weight map preserve the brackets of
elements of the positive skew algebra. -/
theorem weightMap_lie {x y : SkewLieAlgebra β hβ} (hx : x ∈ positiveLieAlgebra β hβ d)
    (hy : y ∈ positiveLieAlgebra β hβ d) :
    weightMap β hβ χ ⁅x, y⁆ = ⁅weightMap β hβ χ x, weightMap β hβ χ y⁆ := by
  have hsupp {z : SkewLieAlgebra β hβ} (hz : z ∈ positiveLieAlgebra β hβ d) {n : Γ}
      (hn : n ∈ (toFinsupp β hβ z).support) : n ∈ d.monoid := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hn ((mem_positiveLieAlgebra_iff β hβ d z).mp hz n (.inl h))
  rw [← sum_single_toFinsupp β hβ x, ← sum_single_toFinsupp β hβ y, sum_lie, map_sum, map_sum,
    sum_lie]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [lie_sum, map_sum, map_sum, lie_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [single_bracket_single, weightMap_single, weightMap_single, weightMap_single,
    single_bracket_single, hχ n (hsupp hx hn) m (hsupp hy hm)]
  congr 1
  ring

variable (d) in
/-- The weight map of a weight multiplicative on the allowed monoid, as a Lie endomorphism of the
positive skew algebra. -/
def weightLieHom : positiveLieAlgebra β hβ d →ₗ⁅R⁆ positiveLieAlgebra β hβ d :=
  { ((weightMap β hβ χ).comp (positiveLieAlgebra β hβ d).incl.toLinearMap).codRestrict
      (positiveLieAlgebra β hβ d).toSubmodule
      fun x => weightMap_mem_positiveLieAlgebra β hβ χ x.property with
    map_lie' := fun {x y} => Subtype.ext (weightMap_lie β hβ hχ x.property y.property) }

/-- Forgetting positive support recovers the ambient weight map. -/
@[simp]
theorem coe_weightLieHom (x : positiveLieAlgebra β hβ d) :
    (weightLieHom β hβ d hχ x).val = weightMap β hβ χ x.val := (rfl)

variable (d) in
/-- The weight map of a weight multiplicative on the allowed monoid, as a graded Lie
endomorphism of fixed degree of the positive skew algebra. -/
def weightGradedLieHom :
    GradedLieHom (PositiveDegreeMap.id d) (positiveGrading β hβ d) (positiveGrading β hβ d) where
  toLieHom := weightLieHom β hβ d hχ
  map_mem {n x} hx := by
    obtain ⟨r, hr⟩ := (mem_grade_iff β hβ n x.val).mp ((mem_positiveGrading_iff β hβ d n x).mp hx)
    refine (mem_positiveGrading_iff β hβ d _ _).mpr ((mem_grade_iff β hβ _ _).mpr ⟨χ n * r, ?_⟩)
    rw [PositiveDegreeMap.id_apply, ← weightMap_single, hr, coe_weightLieHom]

/-- Forgetting positive support recovers the ambient weight map. -/
@[simp]
theorem coe_weightGradedLieHom (x : positiveLieAlgebra β hβ d) :
    (weightGradedLieHom β hβ d hχ x).val = weightMap β hβ χ x.val := (rfl)

section Ray

variable {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

/-- On the ray of an allowed degree `n`, the generator `c X_{(j+1)n}` is multiplied by
`χ(n)^(j+1)`. -/
@[simp]
theorem weightGradedLieHom_rayGenerator (j : ℕ) (c : R) :
    weightGradedLieHom β hβ d hχ (rayGenerator β hβ hn hn0 j c) =
      rayGenerator β hβ hn hn0 j (χ n ^ (j + 1) * c) := by
  have hpow (j : ℕ) : χ ((j + 1) • n) = χ n ^ (j + 1) := by
    induction j with
    | zero => rw [zero_add, one_smul, pow_one]
    | succ j ih =>
      rw [succ_nsmul, hχ _ (d.monoid.nsmul_mem hn _) n hn, ih, ← pow_succ]
  apply Subtype.ext
  rw [coe_weightGradedLieHom, coe_rayGenerator, coe_rayGenerator, weightMap_single, hpow]

/-- The weight map rescales the scalar series of a finite ray potential by `χ(n)`. -/
theorem weightGradedLieHom_rayPartialSum (k : ℕ) (f : PowerSeries R) :
    weightGradedLieHom β hβ d hχ (rayPartialSum β hβ hn hn0 k f) =
      rayPartialSum β hβ hn hn0 k (rescale (χ n) f) := by
  simp only [rayPartialSum_apply, map_sum, weightGradedLieHom_rayGenerator, coeff_rescale]

variable [DecidableEq Γ] [Algebra ℚ R]

/-- The completed weight map sends the ray label of a power series `f` at an allowed degree `n`
to the ray label of `f(χ(n) T)`. -/
@[simp]
theorem completedMap_weightGradedLieHom_rayExp (f : PowerSeries R) :
    (weightGradedLieHom β hβ d hχ).completedMap (rayExp β hβ hn hn0 f) =
      rayExp β hβ hn hn0 (rescale (χ n) f) := by
  apply CompletedGroup.ext
  intro k
  rw [GradedLieHom.projection_completedMap_of_le _ k (a := k) (PositiveDegreeMap.id_modulus k).le,
    projection_rayExp, projection_rayExp, LieHom.bchGroupMap_exp]
  congr 1
  rw [LieIdeal.mkQ_apply, GradedLieHom.truncatedMap_mk, weightGradedLieHom_rayPartialSum,
    LieIdeal.mkQ_apply]

end Ray

end Mei.SkewLieAlgebra
