/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient.Completion
public import Mei.RingTheory.FilteredAlgebra.Positive.Equiv
public import Mei.RingTheory.MvPowerSeries.Positive
public import Mei.RingTheory.FilteredAlgebra.Positive.PowerSeries

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

A scalar power series evaluated at a monomial `z^q` of nonzero unfrozen degree is positive
exactly when all of its coefficients lie in the image of `S`
(`isPositive_completedAeval_single_iff`); this needs no free coordinates. The coefficient of
`z^(i q)` is read at the order `i deg q`, where it survives.
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

omit he in
/-- A power series evaluated at a principal monomial `z^q` of nonzero unfrozen degree is
positive for the image of `S[Q_pr]` exactly when all of its coefficients lie in the image
of `S`. The coefficient of `z^(i q)` is read at the order `i deg q`, where it survives. -/
theorem isPositive_completedAeval_single_iff (φ : S →+* R) (q : Q) (hq : q.val.2 ≠ 0)
    (f : PowerSeries R) :
    (F).IsPositive (mapRingHom Q φ).rangeS
        ((F).completedAeval ⟨_, D.toCompletion_single_mem_completionIdeal_one d q hq⟩ f) ↔
      ∀ i, PowerSeries.coeff i f ∈ φ.rangeS := by
  classical
  constructor
  · intro hf i
    rw [AlgFiltration.isPositive_iff] at hf
    have hq₁ := d.degree_pos ((D.mem_principalCoefficientMonoid d _).mp q.property) hq
    set δ := (d.degree q.val.2).toNat with hδ
    have hδ₁ : 1 ≤ δ := by omega
    have hδz : (δ : ℤ) = d.degree q.val.2 := Int.toNat_of_nonneg (by omega)
    obtain ⟨a, ha, hax⟩ := hf (i * δ)
    rw [AlgFiltration.projection_completedAeval_eq_sum] at hax
    -- The order-`i δ` projection is the class of the finite polynomial `∑ⱼ fⱼ z^(j q)`.
    have hsum : ∑ j ∈ Finset.range (i * δ + 1), PowerSeries.coeff j f •
          (F).projection (i * δ) ((F).toCompletion (single q 1)) ^ j =
        Ideal.Quotient.mk _
          (∑ j ∈ Finset.range (i * δ + 1), single (j • q) (PowerSeries.coeff j f)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [AlgFiltration.projection_toCompletion, ← map_pow, single_pow, one_pow]
      simpa only [smul_single, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk] using
        (map_smul (Ideal.Quotient.mkₐ R ((F).ideal (i * δ + 1))) (PowerSeries.coeff j f)
          (single (j • q) (1 : R))).symm
    rw [hsum, Ideal.Quotient.eq] at hax
    -- The monomial `z^(i q)` has order `i δ`, so it does not occur in the difference.
    have hcoeff : (a - ∑ j ∈ Finset.range (i * δ + 1),
        single (j • q) (PowerSeries.coeff j f)).coeff (i • q) = 0 := by
      by_contra h
      have := (D.mem_principalCoefficientFiltration_ideal_iff d _ _).mp hax (i • q)
        (Finsupp.mem_support_iff.mpr h)
      simp only [AddSubmonoidClass.coe_nsmul, Prod.smul_snd, map_nsmul, nsmul_eq_mul,
        ← hδz] at this
      push_cast at this
      omega
    have hinj : ∀ j, j • q = i • q ↔ j = i := by
      intro j
      refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
      have h₂ := congrArg (fun x : Q => d.degree x.val.2) h
      simp only [AddSubmonoidClass.coe_nsmul, Prod.smul_snd, map_nsmul, nsmul_eq_mul,
        ← hδz] at h₂
      exact_mod_cast (Int.eq_of_mul_eq_mul_right (by omega) h₂)
    have hi : i ∈ Finset.range (i * δ + 1) := Finset.mem_range.mpr (by nlinarith)
    rw [coeff_sub, Finsupp.sub_apply, sub_eq_zero, coeff_sum, Finset.sum_apply'] at hcoeff
    simp only [coeff_single, Finsupp.single_apply, hinj, Finset.sum_ite_eq', hi,
      ite_true] at hcoeff
    obtain ⟨a, rfl⟩ := RingHom.mem_rangeS.mp ha
    rw [coeff_mapRingHom] at hcoeff
    exact RingHom.mem_rangeS.mpr ⟨_, hcoeff⟩
  · intro hf
    refine AlgFiltration.IsPositive.completedAeval
      (AlgFiltration.isPositive_toCompletion
        (RingHom.mem_rangeS.mpr ⟨single q 1, by simp [mapRingHom_single]⟩))
      fun i => ?_
    obtain ⟨s, hs⟩ := RingHom.mem_rangeS.mp (hf i)
    exact RingHom.mem_rangeS.mpr ⟨single 0 s, by simp [mapRingHom_single, hs]⟩

end Mei.SkewLatticeDatum
