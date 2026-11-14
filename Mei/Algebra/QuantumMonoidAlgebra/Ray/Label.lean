/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Action
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Completed
public import Mei.Algebra.Lie.BCH.Ray.Series
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Log

/-!
# Power-series labels on a ray of the positive quantum Lie algebra

Let `n` be a nonzero allowed degree. The quantum monomials `z^((j+1)n)` are homogeneous
elements of the strictly positive quantum Lie algebra, so every power series `f` gives a
completed BCH label `QuantumMonoidAlgebra.rayExp q β hn hn0 f = exp(∑_{j ≥ 1} f_j z^{jn})`,
the generic `PositiveDegrees.rayExp` for this family. For an alternating form, monomials on
rays of degrees that pair to zero commute, so these labels commute
(`QuantumMonoidAlgebra.commute_rayExp`).

For an alternating form and `f` with zero constant coefficient, the coefficient logarithm of
`rayExp f` is the completed evaluation `f(z^n)` at the positive ray generator
(`QuantumMonoidAlgebra.CoefficientAction.coe_completedCoefficientLog_rayExp`). Hence for a
series `G` with constant coefficient one, the label `rayExp (log G)` acts on completed positive
coefficients by conjugation with `G(z^n)`
(`QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_rayExp_logOf`), and on a positive
monomial by `z^p ↦ z^p G(q^(2β(n,p)) z^n) G(z^n)⁻¹`
(`QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_rayExp_logOf_monomial`).

We combine `QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_apply`, the completed
logarithm of `AlgFiltration.completedAeval_logOf` and
`QuantumMonoidAlgebra.completedRay_conj`. The quantum ray action follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(iii),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

open PowerSeries

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) {d : PositiveDegrees Γ}
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

/-- The strictly positive quantum Lie monomial `z^((j+1)n)` of a nonzero allowed degree `n`. -/
def rayLieMonomial (j : ℕ) : positiveLieAlgebra q β d :=
  ⟨monomial q β ((j + 1) • n), grade_le_positiveLieAlgebra q β d (d.monoid.nsmul_mem hn _)
    (d.succ_nsmul_ne_zero hn hn0 j) ((mem_grade_iff q β _ _).mpr ⟨1, one_smul _ _⟩)⟩

/-- The ray Lie monomial is the quantum monomial `z^((j+1)n)`. -/
@[simp]
theorem coe_rayLieMonomial (j : ℕ) :
    (rayLieMonomial q β hn hn0 j : QuantumMonoidAlgebra q β) = monomial q β ((j + 1) • n) :=
  (rfl)

/-- The ray Lie monomial `z^((j+1)n)` is homogeneous of degree `(j+1)n`. -/
theorem rayLieMonomial_mem (j : ℕ) :
    rayLieMonomial q β hn hn0 j ∈ positiveLieGrading q β d ((j + 1) • n) :=
  (mem_positiveLieGrading q β d _ _).mpr ((mem_grade_iff q β _ _).mpr ⟨1, one_smul _ _⟩)

/-- For an alternating form, ray monomials of degrees `n, n'` with `β(n,n') = 0` commute. -/
@[simp]
theorem lie_rayLieMonomial_eq_zero (hβ : β.IsAlt) {n' : Γ} (hn' : n' ∈ d.monoid)
    (hn0' : n' ≠ 0) (h : β n n' = 0) (i j : ℕ) :
    ⁅rayLieMonomial q β hn hn0 i, rayLieMonomial q β hn' hn0' j⁆ = 0 := by
  apply Subtype.ext
  simp [lie_monomial q β hβ, h]

/-- For an alternating form, powers of the positive monomial `z^n` are the monomials `z^(jn)`. -/
theorem positiveMonomial_pow (hβ : β.IsAlt) (p : d.monoid) (j : ℕ) :
    positiveMonomial q β d.monoid p ^ j = positiveMonomial q β d.monoid (j • p) := by
  apply Subtype.ext
  simp [monomial_pow q β hβ]

variable [DecidableEq Γ] [Algebra ℚ R]

local notation "ℒ" => positiveLieGrading q β d

/-- The completed quantum ray label `exp(∑_{j ≥ 1} f_j z^{jn})` of a power series `f`;
the constant coefficient is ignored. -/
def rayExp (f : R⟦X⟧) : d.completedBCHGroup ℒ :=
  d.rayExp ℒ (rayLieMonomial q β hn hn0) hn hn0 (rayLieMonomial_mem q β hn hn0) f

/-- The quantum ray label is the generic power-series label of the ray monomials. -/
theorem rayExp_def (f : R⟦X⟧) :
    rayExp q β hn hn0 f =
      d.rayExp ℒ (rayLieMonomial q β hn hn0) hn hn0 (rayLieMonomial_mem q β hn hn0) f :=
  (rfl)

/-- For an alternating form, quantum ray labels of degrees `n, n'` with `β(n,n') = 0`
commute. -/
theorem commute_rayExp (hβ : β.IsAlt) {n' : Γ} (hn' : n' ∈ d.monoid) (hn0' : n' ≠ 0)
    (h : β n n' = 0) (f g : R⟦X⟧) :
    Commute (rayExp q β hn hn0 f) (rayExp q β hn' hn0' g) :=
  d.commute_rayExp ℒ _ hn hn0 hn' hn0' _ _
    (lie_rayLieMonomial_eq_zero q β hn hn0 hβ hn' hn0' h) f g

local notation "𝓕" => positiveFiltration q β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn)
local notation "ζ" => completedRayGenerator q β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn) (Subtype.mk n hn) (d.degree_pos hn hn0)

namespace CoefficientAction

open scoped CoefficientAction

/-- For an alternating form and a series `f` with zero constant coefficient, the coefficient
logarithm of `rayExp f` is the completed evaluation `f(z^n)`. -/
theorem coe_completedCoefficientLog_rayExp (hβ : β.IsAlt) (f : R⟦X⟧)
    (hf : constantCoeff f = 0) :
    (completedCoefficientLog q β d (rayExp q β hn hn0 f) : (𝓕).completion) =
      (𝓕).completedAeval ζ f := by
  apply (𝓕).completion_ext
  intro k
  -- Both sides are `∑_{j < k} f_{j+1} z^((j+1)n)` modulo the order-`(k+1)` ideal.
  have hl : (𝓕).projection k (completedCoefficientLog q β d (rayExp q β hn hn0 f)) =
      ∑ j ∈ Finset.range k, Ideal.Quotient.mk _
        (positiveLieToCoefficients q β d (coeff (j + 1) f • rayLieMonomial q β hn hn0 j)) := by
    rw [projection_completedCoefficientLog, rayExp_def, d.log_projection_rayExp,
      LieIdeal.mkQ_apply, truncatedCoefficientInclusion_mk,
      PositiveDegrees.rayPartialSum_apply, map_sum, map_sum]
  have hr : (𝓕).projection k ((𝓕).completedAeval ζ f) =
      ∑ j ∈ Finset.range k, coeff (j + 1) f •
        Ideal.Quotient.mk _ (positiveMonomial q β d.monoid ⟨n, hn⟩) ^ (j + 1) := by
    rw [AlgFiltration.projection_completedAeval_eq_sum, Finset.sum_range_succ',
      coeff_zero_eq_constantCoeff_apply, hf, zero_smul, add_zero, coe_completedRayGenerator,
      AlgFiltration.projection_toCompletion]
  rw [hl, hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hm : positiveLieToCoefficients q β d (coeff (j + 1) f • rayLieMonomial q β hn hn0 j) =
      coeff (j + 1) f • positiveMonomial q β d.monoid ⟨n, hn⟩ ^ (j + 1) := by
    rw [positiveMonomial_pow q β hβ]
    exact Subtype.ext (by simp)
  rw [hm, ← Ideal.Quotient.mkₐ_eq_mk R, _root_.map_smul, map_pow]

/-- For an alternating form and a series `G` with constant coefficient one, the exponential
of the coefficient logarithm of `rayExp (log G)` is `G(z^n)`. -/
theorem completedExp_completedCoefficientLog_rayExp_logOf (hβ : β.IsAlt) (G : R⟦X⟧)
    (hG : constantCoeff G = 1) :
    (𝓕).completedExp (completedCoefficientLog q β d (rayExp q β hn hn0 (logOf G))) =
      (𝓕).completedAeval ζ G := by
  have he : completedCoefficientLog q β d (rayExp q β hn hn0 (logOf G)) =
      ⟨(𝓕).completedLog ⟨(𝓕).completedAeval ζ G, (𝓕).completedAeval_sub_one_mem_first ζ G hG⟩,
        (𝓕).completedLog_mem _⟩ := by
    apply Subtype.ext
    rw [coe_completedCoefficientLog_rayExp q β hn hn0 hβ _ (constantCoeff_logOf hG),
      (𝓕).completedAeval_logOf ζ G hG]
  rw [he, AlgFiltration.completedExp_completedLog]

/-- For an alternating form and a series `G` with constant coefficient one, the label
`rayExp (log G)` acts on completed positive coefficients by conjugation with `G(z^n)`. -/
theorem completedBCHAction_rayExp_logOf (hβ : β.IsAlt) (G : R⟦X⟧) (hG : constantCoeff G = 1)
    (a : (𝓕).completion) :
    (𝓕).completedBCHAction d ℒ (rayExp q β hn hn0 (logOf G)) a =
      (𝓕).completedAeval ζ G * a * (𝓕).completedAeval ζ (invOfUnit G 1) := by
  have hG' : constantCoeff (invOfUnit G 1) = 1 := by simp
  -- The inverse label is the label of the logarithm of the inverse series.
  have hinv : (rayExp q β hn hn0 (logOf G))⁻¹ = rayExp q β hn hn0 (logOf (invOfUnit G 1)) := by
    have hlog : logOf (invOfUnit G 1) = -logOf G := by
      rw [eq_neg_iff_add_eq_zero, ← logOf_mul hG' hG, invOfUnit_mul G 1 (by simp [hG]),
        logOf_one]
    rw [hlog, rayExp_def, rayExp_def, PositiveDegrees.rayExp_neg]
  rw [completedBCHAction_apply, hinv,
    completedExp_completedCoefficientLog_rayExp_logOf q β hn hn0 hβ G hG,
    completedExp_completedCoefficientLog_rayExp_logOf q β hn hn0 hβ _ hG']

/-- The quantum ray action: for an alternating form and a series `G` with constant
coefficient one, `rayExp (log G)` sends a positive monomial `z^p` to
`z^p G(q^(2β(n,p)) z^n) G(z^n)⁻¹`. -/
theorem completedBCHAction_rayExp_logOf_monomial (hβ : β.IsAlt) (G : R⟦X⟧)
    (hG : constantCoeff G = 1) (p : d.monoid) :
    (𝓕).completedBCHAction d ℒ (rayExp q β hn hn0 (logOf G))
        ((𝓕).toCompletion (positiveMonomial q β d.monoid p)) =
      (𝓕).toCompletion (positiveMonomial q β d.monoid p) *
        (𝓕).completedAeval ζ (rescale ((q ^ (2 * β n p) : Rˣ) : R) G * invOfUnit G 1) := by
  let U : R⟦X⟧ˣ := ⟨G, invOfUnit G 1, mul_invOfUnit G 1 (by simp [hG]),
    invOfUnit_mul G 1 (by simp [hG])⟩
  rw [completedBCHAction_rayExp_logOf q β hn hn0 hβ G hG]
  exact completedRay_conj q β d.monoid d.degree (fun _ hn => d.degree_nonneg hn) hβ ⟨n, hn⟩ p
    (d.degree_pos hn hn0) U

end CoefficientAction

end Mei.QuantumMonoidAlgebra
