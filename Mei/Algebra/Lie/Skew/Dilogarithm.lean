/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Skew.Ray
public import Mei.RingTheory.PowerSeries.Dilogarithm

/-!
# Dilogarithm elements of the completed skew group

For a nonzero allowed degree `n` of positive degree data on the exponent group of a skew
Lie algebra over a commutative `ℚ`-algebra, the dilogarithm element is
`Ψ[n] = exp(∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` in the completed BCH group. It is the
ray label of the power series `-Li₂(-X)` (`PowerSeries.negDilogNeg`): at order `k` it is
the exponential of the class of the finite sum over `j ≤ k`, and these levelwise
exponentials are compatible under truncation. Its logarithmic coefficients are
`(-1)^(j+1)/j² X_{jn}` on the positive multiples of `n` and zero elsewhere.

`Ψ[n]` lies in the completed subgroup of the supported ray through `n`, so dilogarithm
elements of degrees on one ray commute. Rational powers, such as the normalized factors
`Ψ[tn]^(s κ(tn))`, are given by the ray labels `rayExp (c • negDilogNeg R)`; for integers
`c` these are the group powers, by `rayExp_zsmul`.

The elements and their conventions follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2), and Nakanishi, *Cluster algebras and scattering
diagrams, Part III*, §5.1 (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

local notation "𝔤" => positiveLieAlgebra β hβ d
local notation "ℒ" => positiveGrading β hβ d

/-- The dilogarithm element `Ψ[n] = exp(∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of a nonzero
allowed degree `n`, in the completed BCH group of the positive skew Lie algebra. -/
def dilogElement : d.completedBCHGroup ℒ :=
  rayExp β hβ hn hn0 (negDilogNeg R)

theorem dilogElement_def : dilogElement β hβ hn hn0 = rayExp β hβ hn hn0 (negDilogNeg R) :=
  (rfl)

/-- At order `k`, `Ψ[n]` is the exponential of the class of
`∑_{j < k} (-1)^j / (j+1)² X_{(j+1)n}`. -/
theorem projection_dilogElement (k : ℕ) :
    CompletedGroup.projection k (dilogElement β hβ hn hn0) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ (∑ j ∈ Finset.range k,
        rayGenerator β hβ hn hn0 j (algebraMap ℚ R ((-1) ^ j / ((j : ℚ) + 1) ^ 2)))) := by
  simp only [dilogElement, projection_rayExp, rayPartialSum_apply, coeff_succ_negDilogNeg]
  -- Both sides are the same exponential, typed in the tower object and the truncated group.
  rfl

/-- The logarithmic coefficient of `Ψ[n]` in degree `(j+1)n` is
`(-1)^j / (j+1)² X_{(j+1)n}`. -/
@[simp]
theorem logComponent_dilogElement_succ_nsmul (j : ℕ) :
    (d.logComponent ℒ (dilogElement β hβ hn hn0) ((j + 1) • n) : 𝔤) =
      rayGenerator β hβ hn hn0 j (algebraMap ℚ R ((-1) ^ j / ((j : ℚ) + 1) ^ 2)) := by
  rw [dilogElement, logComponent_rayExp_succ_nsmul, coeff_succ_negDilogNeg]

/-- Off the positive multiples of `n`, `Ψ[n]` has no logarithmic coefficient. -/
theorem logComponent_dilogElement_eq_zero_of_forall_ne {m : Γ} (hm : ∀ j : ℕ, (j + 1) • n ≠ m) :
    d.logComponent ℒ (dilogElement β hβ hn hn0) m = 0 :=
  logComponent_rayExp_eq_zero_of_forall_ne β hβ hn hn0 _ hm

/-- `Ψ[n]` lies in the completed subgroup of the supported ray through `n`. -/
theorem dilogElement_mem_completedRaySubgroup {w : SupportedRay d} (hw : n ∈ w.rayDegrees) :
    dilogElement β hβ hn hn0 ∈ d.completedRaySubgroup ℒ w :=
  rayExp_mem_completedRaySubgroup β hβ hn hn0 hw _

/-- Dilogarithm elements of degrees on one supported ray commute. -/
theorem commute_dilogElement {n' : Γ} (hn' : n' ∈ d.monoid) (hn0' : n' ≠ 0)
    {w : SupportedRay d} (hw : n ∈ w.rayDegrees) (hw' : n' ∈ w.rayDegrees) :
    Commute (dilogElement β hβ hn hn0) (dilogElement β hβ hn' hn0') :=
  d.commute_of_mem_completedRaySubgroup ℒ (dilogElement_mem_completedRaySubgroup β hβ hn hn0 hw)
    (dilogElement_mem_completedRaySubgroup β hβ hn' hn0' hw')

end Mei.SkewLieAlgebra
