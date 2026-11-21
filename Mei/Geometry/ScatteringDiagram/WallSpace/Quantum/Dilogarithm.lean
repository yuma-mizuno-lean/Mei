/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.PowerSeriesLabel
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Label
public import Mei.RingTheory.PowerSeries.LogQuantumDilogarithm

/-!
# Quantum dilogarithm wall labels

Let `β` be an integral alternating form, `n` an actual degree of a supported ray `w`, and `m` a
nonzero integral normal with the kernel of `β(n,-)`. Every quantum ray label
`QuantumMonoidAlgebra.rayExp q β hn hn0 f = exp(∑_{j ≥ 1} f_j z^{jn})` is then a wall label for
`w` and `m` (`QuantumMonoidAlgebra.rayExp_mem_wallGroup`), since each monomial `z^((j+1)n)` lies
in the quantum wall space of degree `(j+1)n` and normal `m`.

If every `q^k - q^(-k)`, `k > 0`, is a unit, the quantum dilogarithm label
`QuantumMonoidAlgebra.quantumDilogLabel` is the wall label `exp(log Ψ_q(z^n))`. Its logarithmic
coefficient in degree `kn`, `k > 0`, is `(-1)^(k-1) z^{kn} / (k (q^k - q^(-k)))`
(`QuantumMonoidAlgebra.logComponent_quantumDilogLabel`). It acts on completed positive
coefficients by conjugation with `Ψ_q(z^n)`
(`QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_quantumDilogLabel`), so on a positive
monomial `z^p` with `r = β(n,p)` by multiplication with `∏_{j < r} (1 + q^(2j+1) z^n)` for
`r ≥ 0` and with the product of the inverses of `1 + q^(-(2j+1)) z^n`, `j < -r`, for `r ≤ 0`.

We combine `DirectedWallSpaces.rayExp_mem_wallGroup`,
`Units.coeff_succ_logOf_quantumDilogarithm`,
`QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_rayExp_logOf` and
`QuantumMonoidAlgebra.completedRay_quantumDilogarithm_conj`. The conventions are those of
Nakanishi, *Pentagon relation in quantum cluster scattering diagrams*, §2.3,
arXiv:2202.01588v7, and the quantum wall spaces of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(iii), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

open PowerSeries

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) {m : Γ →+ ℤ}
  (hm : m ≠ 0) (hker : m.ker = (β n).toAddMonoidHom.ker)

include hm hker in
/-- If `m` is a nonzero normal with the kernel of `β(n,-)`, the monomial `z^((j+1)n)` lies in
the quantum wall space of degree `(j+1)n` and normal `m`. -/
theorem rayLieMonomial_mem_wallSpaces (j : ℕ) :
    rayLieMonomial q β hn hn0 j ∈ (wallSpaces q β d hβ).wall ((j + 1) • n) m := by
  have hk : (β ((j + 1) • n)).toAddMonoidHom.ker = (β n).toAddMonoidHom.ker := by
    ext v
    simp [Nat.cast_add_one_ne_zero]
  rw [wallSpaces_wall, Submodule.mem_comap, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    mem_wallSubmodule_iff]
  exact Or.inr ⟨hm, hker.trans hk.symm,
    (mem_positiveLieGrading q β d _ _).mp (rayLieMonomial_mem q β hn hn0 j)⟩

variable [DecidableEq Γ] [Algebra ℚ R]

include hm hker in
/-- If `n` is a degree of the supported ray `w` and `m` is a nonzero normal with the kernel of
`β(n,-)`, every quantum ray label on `n` is a quantum wall label for `w` and `m`. -/
theorem rayExp_mem_wallGroup {w : SupportedRay d} (hw : n ∈ w.rayDegrees) (f : R⟦X⟧) :
    rayExp q β hn hn0 f ∈ (wallSpaces q β d hβ).wallGroup w m := by
  rw [rayExp_def]
  exact (wallSpaces q β d hβ).rayExp_mem_wallGroup hn hn0 _ hw
    (rayLieMonomial_mem_wallSpaces q β hβ hn hn0 hm hker) f

variable (hq : ∀ k : ℕ, IsUnit ((q : R) ^ (k + 1) - (↑q⁻¹ : R) ^ (k + 1)))
  {w : SupportedRay d} (hw : n ∈ w.rayDegrees)

/-- The quantum dilogarithm wall label `exp(log Ψ_q(z^n))` on a degree `n` of the supported
ray `w`, with a nonzero normal `m` having the kernel of `β(n,-)`. -/
def quantumDilogLabel : (wallSpaces q β d hβ).wallGroup w m :=
  ⟨rayExp q β (w.rayDegrees_subset hw) (SupportedRay.ne_zero_of_mem_rayDegrees hw)
      (logOf (q.quantumDilogarithm hq)),
    rayExp_mem_wallGroup q β hβ _ _ hm hker hw _⟩

/-- The quantum dilogarithm wall label is the quantum ray label of `log Ψ_q`. -/
@[simp]
theorem coe_quantumDilogLabel :
    (quantumDilogLabel q β hβ hm hker hq hw : d.completedBCHGroup (positiveLieGrading q β d)) =
      rayExp q β (w.rayDegrees_subset hw) (SupportedRay.ne_zero_of_mem_rayDegrees hw)
        (logOf (q.quantumDilogarithm hq)) :=
  (rfl)

/-- The logarithmic coefficient of the quantum dilogarithm label in degree `(k+1)n` is
`(-1)^k z^((k+1)n) / ((k + 1) (q^(k+1) - q^(-(k+1))))`. -/
theorem logComponent_quantumDilogLabel (k : ℕ) :
    ((d.logComponent (positiveLieGrading q β d) (quantumDilogLabel q β hβ hm hker hq hw)
        ((k + 1) • n) : positiveLieAlgebra q β d) : QuantumMonoidAlgebra q β) =
      (algebraMap ℚ R ((-1 : ℚ) ^ k / (k + 1)) *
        Ring.inverse ((q : R) ^ (k + 1) - (↑q⁻¹ : R) ^ (k + 1))) •
          monomial q β ((k + 1) • n) := by
  rw [coe_quantumDilogLabel, rayExp_def, PositiveDegrees.logComponent_rayExp_succ_nsmul,
    Units.coeff_succ_logOf_quantumDilogarithm]
  simp

namespace CoefficientAction

open scoped CoefficientAction

local notation "𝓕" => positiveFiltration q β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn)
local notation "ζ" => completedRayGenerator q β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn) (Subtype.mk n (w.rayDegrees_subset hw))
  (d.degree_pos (w.rayDegrees_subset hw) (SupportedRay.ne_zero_of_mem_rayDegrees hw))

/-- The quantum dilogarithm wall label acts on completed positive coefficients by
conjugation with `Ψ_q(z^n)`. -/
theorem completedBCHAction_quantumDilogLabel (a : (𝓕).completion) :
    (𝓕).completedBCHAction d (positiveLieGrading q β d)
        (quantumDilogLabel q β hβ hm hker hq hw) a =
      (𝓕).completedAeval ζ (q.quantumDilogarithm hq) * a *
        (𝓕).completedAeval ζ (invOfUnit (q.quantumDilogarithm hq) 1) := by
  rw [coe_quantumDilogLabel]
  exact completedBCHAction_rayExp_logOf q β _ _ hβ _
    (Units.constantCoeff_quantumDilogarithm q hq) a

/-- For `β(n,p) = r ≥ 0`, the quantum dilogarithm wall label multiplies the positive monomial
`z^p` by `∏_{j < r} (1 + q^(2j+1) z^n)`. -/
theorem completedBCHAction_quantumDilogLabel_monomial_of_nonneg (p : d.monoid) (r : ℕ)
    (hr : β n p = r) :
    (𝓕).completedBCHAction d (positiveLieGrading q β d)
        (quantumDilogLabel q β hβ hm hker hq hw)
        ((𝓕).toCompletion (positiveMonomial q β d.monoid p)) =
      (𝓕).toCompletion (positiveMonomial q β d.monoid p) *
        ((List.range r).map fun j => 1 + (q : R) ^ (2 * j + 1) • (ζ : (𝓕).completion)).prod := by
  rw [completedBCHAction_quantumDilogLabel]
  exact completedRay_quantumDilogarithm_conj q β d.monoid d.degree
    (fun _ hn => d.degree_nonneg hn) hq hβ ⟨n, (w.rayDegrees_subset hw)⟩ p _ r hr

/-- For `β(n,p) = -r ≤ 0`, the quantum dilogarithm wall label multiplies the positive monomial
`z^p` by the product of the inverses of `1 + q^(-(2j+1)) z^n`, `j < r`. -/
theorem completedBCHAction_quantumDilogLabel_monomial_of_nonpos (p : d.monoid) (r : ℕ)
    (hr : β n p = -(r : ℤ)) :
    (𝓕).completedBCHAction d (positiveLieGrading q β d)
        (quantumDilogLabel q β hβ hm hker hq hw)
        ((𝓕).toCompletion (positiveMonomial q β d.monoid p)) =
      (𝓕).toCompletion (positiveMonomial q β d.monoid p) *
        ((List.range r).map fun j =>
          Ring.inverse (1 + (↑q⁻¹ : R) ^ (2 * j + 1) • (ζ : (𝓕).completion))).prod := by
  rw [completedBCHAction_quantumDilogLabel]
  exact completedRay_quantumDilogarithm_conj_neg q β d.monoid d.degree
    (fun _ hn => d.degree_nonneg hn) hq hβ ⟨n, (w.rayDegrees_subset hw)⟩ p _ r hr

end CoefficientAction

end Mei.QuantumMonoidAlgebra
