/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Quantum.Basic
public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Algebra.QuantumMonoidAlgebra.Dilogarithm
public import Mei.Algebra.QuantumMonoidAlgebra.Specialization
public import Mei.LinearAlgebra.Determinant.Prod

/-!
# Examples of quantum dilogarithm diagrams

Take `Γ = ℤ²` with the positive quadrant `ℕ²` and the alternating form `β = det`, so that
`β(e₁, e₂) = 1`, and the supported ray `w` through `e₁`. The functional `β(e₁,-)` is the second
coordinate `e₂*`, which is therefore an eligible quantum normal for `e₁`.

* Over `ℚ` with `q = 2`, every `q^k - q^(-k)`, `k > 0`, is a unit
  (`QuantumHyperplaneInput.Examples.isUnit_two_pow_sub_inv_pow`). The quantum dilogarithm label
  `θ = exp(log Ψ_q(z^{e₁}))` has linear logarithmic coefficient `z^{e₁} / (q - q⁻¹) = (2/3) z^{e₁}`
  (`QuantumHyperplaneInput.Examples.logComponent_label_e₁`), and it acts on the monomial
  `z^{e₂}` of pairing `β(e₁, e₂) = 1` by `θ(z^{e₂}) = z^{e₂} + z^{e₂ + e₁}`
  (`QuantumHyperplaneInput.Examples.completedBCHAction_label_e₂`).
* The two horizontal lines `{y = 0}` and `{y = 1}`, both with the dilogarithm label of `e₁`, form
  a quantum dilogarithm input in the commuting case `β(e₁, e₁) = 0`; its quantum *Scat* is its
  own class (`QuantumHyperplaneInput.Examples.scat_parallelLines`).
* Over the Laurent ring `ℚ[T, T⁻¹]` with `q = T`, the same lines labelled by `exp(z^{e₁})`
  specialize along `T ↦ 1` to a quantum diagram at `q = 1`, all of whose labels act trivially on
  completed coefficients (`QuantumHyperplaneInput.Examples.completedBCHAction_atOne_parallelLines`).
-/

public section

noncomputable section

namespace Mei.QuantumHyperplaneInput.Examples

open QuantumMonoidAlgebra PowerSeries TauCeti.Toric

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The supported ray through `e₁ = (1, 0)` in the positive quadrant. -/
def horizontalRay : SupportedRay ℕ² :=
  Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 0

/-- The basis vector `e₁ = (1, 0)` lies on the horizontal ray. -/
theorem e₁_mem_rayDegrees : ((1, 0) : ℤ × ℤ) ∈ horizontalRay.rayDegrees := by
  simpa [horizontalRay] using (horizontalRay.generator_mem_rayDegrees_iff).mpr
    (by simp [horizontalRay])

/-- The determinant form `det(x, y) = x₁ y₂ - x₂ y₁` on `ℤ²` is alternating. -/
theorem isAlt_det : LinearMap.BilinForm.IsAlt (Prod.det (R := ℤ)) :=
  Prod.isAlt_det

/-- The second coordinate `e₂*` is nonzero. -/
theorem snd_ne_zero : AddMonoidHom.snd ℤ ℤ ≠ 0 := fun he => by
  simpa using DFunLike.congr_fun he (0, 1)

/-- The second coordinate `e₂*` has the kernel of `det(e₁, -)`. -/
theorem ker_snd : (AddMonoidHom.snd ℤ ℤ).ker = (Prod.det ((1, 0) : ℤ × ℤ)).toAddMonoidHom.ker := by
  ext v
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
    Prod.det_apply]
  simp

/-- The horizontal lines `{y = 0}` and `{y = 1}`, both with degree `e₁` and normal `e₂*`. -/
def parallelLines : QuantumHyperplaneInput Prod.det ℕ² (Fin 2) where
  ray _ := horizontalRay
  degree _ := (1, 0)
  degree_mem _ := e₁_mem_rayDegrees
  normal _ := AddMonoidHom.snd ℤ ℤ
  normal_ne_zero _ := snd_ne_zero
  ker_normal _ := ker_snd
  offset j := j.val

/-- The quantum parameter `q = 2` over `ℚ`. -/
def two : ℚˣ := Units.mk0 2 two_ne_zero

/-- For `q = 2`, every `q^(k+1) - q^(-(k+1))` is a unit of `ℚ`. -/
theorem isUnit_two_pow_sub_inv_pow (k : ℕ) :
    IsUnit ((two : ℚ) ^ (k + 1) - (↑two⁻¹ : ℚ) ^ (k + 1)) := by
  refine isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt ?_))
  simp only [two, Units.val_inv_eq_inv_val, Units.val_mk0]
  calc (2⁻¹ : ℚ) ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) k.succ_ne_zero
    _ < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) k.succ_ne_zero

/-- The quantum dilogarithm label `exp(log Ψ_2(z^{e₁}))` on the horizontal ray. -/
local notation "θ" => quantumDilogLabel two Prod.det isAlt_det snd_ne_zero ker_snd
  isUnit_two_pow_sub_inv_pow e₁_mem_rayDegrees

open scoped CoefficientAction

/-- The linear logarithmic coefficient of `θ` is `z^{e₁} / (q - q⁻¹) = (2/3) z^{e₁}`. -/
theorem logComponent_label_e₁ :
    ((ℕ².logComponent (positiveLieGrading two Prod.det ℕ²) θ ((0 + 1) • ((1, 0) : ℤ × ℤ)) :
        positiveLieAlgebra two Prod.det ℕ²) : QuantumMonoidAlgebra two Prod.det) =
      (2 / 3 : ℚ) • monomial two Prod.det (1, 0) := by
  rw [logComponent_quantumDilogLabel]
  norm_num [two, Ring.inverse_eq_inv']

/-- The label `θ` sends the monomial `z^{e₂}`, of pairing `det(e₁, e₂) = 1`, to
`z^{e₂} + z^{e₂ + e₁}`. -/
theorem completedBCHAction_label_e₂ :
    (positiveFiltration two Prod.det ℕ².monoid ℕ².degree
      (fun _ hn => ℕ².degree_nonneg hn)).completedBCHAction ℕ² (positiveLieGrading two Prod.det ℕ²)
        θ ((positiveFiltration two Prod.det ℕ².monoid ℕ².degree
          (fun _ hn => ℕ².degree_nonneg hn)).toCompletion
            (positiveMonomial two Prod.det ℕ².monoid ⟨(0, 1), by simp⟩)) =
      (positiveFiltration two Prod.det ℕ².monoid ℕ².degree
          (fun _ hn => ℕ².degree_nonneg hn)).toCompletion
        (positiveMonomial two Prod.det ℕ².monoid ⟨(0, 1), by simp⟩) +
      (positiveFiltration two Prod.det ℕ².monoid ℕ².degree
          (fun _ hn => ℕ².degree_nonneg hn)).toCompletion
        (positiveMonomial two Prod.det ℕ².monoid (⟨(0, 1), by simp⟩ + ⟨(1, 0), by simp⟩)) := by
  rw [CoefficientAction.completedBCHAction_quantumDilogLabel,
    AlgFiltration.completedAeval_invOfUnit _ _ _ 1 (Units.constantCoeff_quantumDilogarithm _ _)]
  have hc := quantumDilogarithm_conj_of_pairing_one two Prod.det isAlt_det ℕ².monoid ℕ².degree
    (fun _ hn => ℕ².degree_nonneg hn) ⟨(1, 0), by simp⟩ (by simp) isUnit_two_pow_sub_inv_pow
    ⟨(0, 1), by simp⟩ (by simp)
  simp only [AlgFiltration.toCompletionₐ_apply] at hc
  -- The ray generator is the completed monomial `z^{e₁}` used by the monomial expansion.
  convert hc using 4 <;> exact congrArg _ (Subtype.ext (coe_completedRayGenerator ..))

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The two horizontal lines with the dilogarithm label of `e₁` are in the commuting case
`det(e₁, e₁) = 0`, so their quantum *Scat* is their own class. -/
theorem scat_parallelLines :
    (parallelLines.dilogDiagram isAlt_det h two isUnit_two_pow_sub_inv_pow).Scat
        (parallelLines.dilogDiagram_full isAlt_det h two isUnit_two_pow_sub_inv_pow) =
      (parallelLines.dilogDiagram isAlt_det h two
        isUnit_two_pow_sub_inv_pow).toClass :=
  parallelLines.scat_dilogDiagram_eq_toClass isAlt_det h two isUnit_two_pow_sub_inv_pow
    fun _ _ => isAlt_det _

/-- The Laurent quantum parameter `q = T` of `ℚ[T, T⁻¹]`. -/
local notation "qT" => IsUnit.unit (LaurentPolynomial.isUnit_T (R := ℚ) 1)

/-- Evaluation `T ↦ 1` sends `q = T` to one. -/
theorem map_qT_zpow (p r : ℤ × ℤ) :
    Units.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1).toMonoidHom (qT ^ Prod.det p r) =
      1 ^ Prod.det p r :=
  Units.ext (by simp)

/-- The quantum ray label `exp(z^{e₁})` over `ℚ[T, T⁻¹]`, a wall label for the normal `e₂*`. -/
def expLabel : (wallSpaces qT Prod.det ℕ² isAlt_det).wallGroup horizontalRay
    (AddMonoidHom.snd ℤ ℤ) :=
  ⟨rayExp qT Prod.det (horizontalRay.rayDegrees_subset e₁_mem_rayDegrees)
    (SupportedRay.ne_zero_of_mem_rayDegrees e₁_mem_rayDegrees) X,
    rayExp_mem_wallGroup qT Prod.det isAlt_det _ _ snd_ne_zero ker_snd e₁_mem_rayDegrees X⟩

/-- The two horizontal lines over `ℚ[T, T⁻¹]`, labelled by `exp(z^{e₁})`. -/
def expLines : DirectedDiagram (d := ℕ²) h (wallSpaces qT Prod.det ℕ² isAlt_det) (Fin 2) :=
  parallelLines.diagram h qT fun _ => expLabel

/-- Over `ℚ[T, T⁻¹]`, the two horizontal lines labelled by `exp(z^{e₁})` specialize along
`T ↦ 1` to a quantum diagram at `q = 1`, all of whose labels act trivially. -/
theorem completedBCHAction_atOne_parallelLines
    (a : (positiveFiltration (1 : ℚˣ) Prod.det ℕ².monoid ℕ².degree
      (fun _ hn => ℕ².degree_nonneg hn)).completion) (j : Fin 2) :
    (positiveFiltration (1 : ℚˣ) Prod.det ℕ².monoid ℕ².degree
      (fun _ hn => ℕ².degree_nonneg hn)).completedBCHAction ℕ²
        (positiveLieGrading (1 : ℚˣ) Prod.det ℕ²)
        ((((expLines h).quantumMap
          (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) map_qT_zpow).wall j).label) a = a :=
  CoefficientAction.completedBCHAction_atOne Prod.det ℕ² _ a

end Mei.QuantumHyperplaneInput.Examples
