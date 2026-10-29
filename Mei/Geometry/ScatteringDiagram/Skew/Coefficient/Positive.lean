/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient.Completion
public import Mei.RingTheory.FilteredAlgebra.Positive.Equiv
public import Mei.RingTheory.MvPowerSeries.Positive

/-!
# Positive principal coefficients

For a coefficient map `S →+* R`, an element of the completed principal coefficient
algebra `R[[Q_pr]]`, with its native positive-increment filtration, is positive with
respect to the image of `S[Q_pr]` exactly when every coefficient of every
character-and-positive-degree monomial `z^m t^n` lies in the image of `S`.
For coefficients `ℚ[A]` and the positive subsemiring `ℕ[A][Q_pr]` this says that
every monomial coefficient is a polynomial with natural-number coefficients, the
positivity notion for wall functions in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), and
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1
(arXiv:2503.03719v1).

The criteria transfer `Mei.AlgFiltration.isPositive_principalCompletion_iff` and
its `ℕ[A]` form through the free-coordinate identification of the native filtration
with the powers of the ideal of variables (`principalCoefficientCompletionEquiv`),
using `Mei.AlgFiltration.isPositive_completionEquiv_iff`. The polynomial dictionary
matches the image of `S[Q_pr]` with the image of `S[M°][t]` because it is natural in
the scalar ring. In the coordinates of an adapted basis this reads positivity in
`ℚ[A][M°][[t_i]]`. Coefficient maps need not be injective, characters have
filtration order zero, and the skew form may be degenerate.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open _root_.AddMonoidAlgebra

variable {N S R ι : Type*} [AddCommGroup N] [CommSemiring S] [CommRing R] [Finite ι]
  (D : SkewLatticeDatum N) (d : PositiveDegrees D.unfrozen)
  (e : d.monoid ≃+ (ι →₀ ℕ)) (he : ∀ n : d.monoid, d.degree n = ((e n).degree : ℤ))

local notation "M" => Module.Dual ℤ D.sublattice
local notation "Q" => D.principalCoefficientMonoid d
local notation "F" => TropicalVertexCoefficientAction.filtration
  (R := R) (D.principalPositiveDegrees d) Q

include he

/-- Positivity in the completed principal coefficient algebra, for the image of
`S[Q_pr]`, is coefficientwise: every coefficient of every monomial `z^m t^n` lies in
the image of `S`. No common finite lift of the whole series is required. -/
theorem isPositive_principalCoefficientCompletion_iff (φ : S →+* R) (x : (F).completion) :
    (F).IsPositive (mapRingHom Q φ).rangeS x ↔
      ∀ (n : ι →₀ ℕ) (m : M),
        (MvPowerSeries.coeff n (D.principalCoefficientCompletionEquiv d e he x)).coeff m ∈
          φ.rangeS := by
  rw [principalCoefficientCompletionEquiv_apply,
    ← AlgFiltration.isPositive_completionEquiv_iff _
      (AlgFiltration.ofIdeal (MvPolynomial.idealOfVars ι R[M]))
      (D.principalCoefficientPolynomialEquiv d e)
      (by simpa only [AlgFiltration.ofIdeal_ideal] using
        D.comap_idealOfVars_pow_principalCoefficientPolynomialEquiv (R := R) d e he)
      (D.principalCoefficientPolynomialEquiv_mem_rangeS_iff d e φ),
    AlgFiltration.isPositive_principalCompletion_iff]
  refine forall_congr' fun n => ?_
  exact Set.ext_iff.mp (AddMonoidAlgebra.range_map φ.toAddMonoidHom) _

/-- For principal coefficients over `ℚ[A]`, positivity with respect to `ℕ[A][Q_pr]`
means that every coefficient of every monomial `z^m t^n` is a polynomial in the
variables `A` with natural-number coefficients. -/
theorem isPositive_principalCoefficientCompletion_natPolynomial_iff {A : Type*}
    (x : (TropicalVertexCoefficientAction.filtration (R := MvPolynomial A ℚ)
      (D.principalPositiveDegrees d) Q).completion) :
    (TropicalVertexCoefficientAction.filtration (R := MvPolynomial A ℚ)
      (D.principalPositiveDegrees d) Q).IsPositive
        (mapRingHom Q (MvPolynomial.map (σ := A) (Nat.castRingHom ℚ))).rangeS x ↔
      ∀ (n : ι →₀ ℕ) (m : M) (a : A →₀ ℕ), ∃ c : ℕ,
        ((MvPowerSeries.coeff n (D.principalCoefficientCompletionEquiv d e he x)).coeff m).coeff
          a = c := by
  rw [principalCoefficientCompletionEquiv_apply,
    ← AlgFiltration.isPositive_completionEquiv_iff _
      (AlgFiltration.ofIdeal (MvPolynomial.idealOfVars ι (MvPolynomial A ℚ)[M]))
      (D.principalCoefficientPolynomialEquiv d e)
      (by simpa only [AlgFiltration.ofIdeal_ideal] using
        D.comap_idealOfVars_pow_principalCoefficientPolynomialEquiv (R := MvPolynomial A ℚ) d e he)
      (D.principalCoefficientPolynomialEquiv_mem_rangeS_iff d e _),
    AlgFiltration.isPositive_principalCompletion_natPolynomial_iff]

omit he in
variable {D} in
/-- In the coordinates of an adapted basis, positivity in `ℚ[A][M°][[t_i]]` with respect
to `ℕ[A][Q_pr]` means that every coefficient of every monomial `z^m t^n` is a polynomial
in the variables `A` with natural-number coefficients. -/
theorem AdaptedBasis.isPositive_principalCoefficientCompletion_natPolynomial_iff
    {J A : Type*} (B : D.AdaptedBasis J)
    (x : (TropicalVertexCoefficientAction.filtration (R := MvPolynomial A ℚ)
      (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees)
      (D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees)).completion) :
    (TropicalVertexCoefficientAction.filtration (R := MvPolynomial A ℚ)
      (D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees)
      (D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees)).IsPositive
        (mapRingHom (D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees)
          (MvPolynomial.map (σ := A) (Nat.castRingHom ℚ))).rangeS x ↔
      ∀ (n : B.unfrozenIndex →₀ ℕ) (m : M) (a : A →₀ ℕ), ∃ c : ℕ,
        ((MvPowerSeries.coeff n (B.principalCoefficientCompletionEquiv x)).coeff m).coeff
          a = c := by
  rw [AdaptedBasis.principalCoefficientCompletionEquiv_def]
  exact D.isPositive_principalCoefficientCompletion_natPolynomial_iff _ _ _ x

end Mei.SkewLatticeDatum
