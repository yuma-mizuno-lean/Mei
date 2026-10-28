/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.MvPowerSeries.Completion
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Positive coefficients in polynomial completions

For a coefficient map `S →+* R`, positivity in the ideal-of-variables completion
with respect to the image of `S[σ]` is equivalent to every coefficient of the
associated multivariate power series belonging to the image of `S`.
The forward implication reads a coefficient from any sufficiently large quotient;
the reverse implication uses total-degree truncation as a positive representative.

In particular, for principal series with coefficients in `ℚ[A][M]`, positivity
with respect to the image of `ℕ[A][M][σ]` says precisely that every coefficient
of every Laurent monomial and coefficient-variable monomial is a natural number.
The lattice monomials can have arbitrary exponents: only the variables `σ` are
completed. This is the coefficient notion used for positive wall functions in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), and Burcroff–Lee–Mou, *Positivity of generalized cluster
scattering diagrams*, §8.1 (arXiv:2503.03719v1).

The construction uses `principalCompletionEquiv`, Mathlib's polynomial coefficient
range criterion, and `AddMonoidAlgebra.range_map`. Coefficient maps need not be
injective, and the positive coefficient semiring need not be a ring.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

variable {σ S R : Type*} [Finite σ] [CommSemiring S] [CommRing R]

/-- Positivity in a polynomial completion is coefficientwise membership in the
image of the coefficient semiring. In particular, no common polynomial lift of
the entire infinite series is required. -/
@[simp]
theorem isPositive_principalCompletion_iff
    (x : (ofIdeal (MvPolynomial.idealOfVars σ R)).completion) (φ : S →+* R) :
    (ofIdeal (MvPolynomial.idealOfVars σ R)).IsPositive
      (MvPolynomial.map (σ := σ) φ).rangeS x ↔
        ∀ n, MvPowerSeries.coeff n (principalCompletionEquiv σ R x) ∈ φ.rangeS := by
  rw [isPositive_iff]
  constructor
  · intro hx n
    obtain ⟨p, ⟨q, rfl⟩, hp⟩ := hx n.degree
    rw [coeff_principalCompletionEquiv_eq_of_projection_eq σ R x n.degree _ hp n le_rfl]
    exact ⟨q.coeff n, MvPolynomial.coeff_map φ q n |>.symm⟩
  · intro hx k
    refine ⟨(principalCompletionEquiv σ R x).truncTotal (k + 1), ?_,
      mk_truncTotal_principalCompletionEquiv σ R k x⟩
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨n, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs
    · exact hx n
    · exact ⟨0, map_zero φ⟩

variable {A M : Type*} [AddCommMonoid M]

local notation "B" => AddMonoidAlgebra (MvPolynomial A ℚ) M

-- Prefer the inherited semiring for coefficient maps and ideal quotients, avoiding
-- repeated comparison of the nested monoid-algebra instances.
attribute [local instance 2000] CommRing.toCommSemiring

local notation "natMap" =>
  (AddMonoidAlgebra.mapRingHom M (MvPolynomial.map (σ := A) (Nat.castRingHom ℚ)) :
    AddMonoidAlgebra (MvPolynomial A ℕ) M →+* B)

/-- For principal series with Laurent coefficients in `ℚ[A][M]`, positivity
means that every scalar monomial coefficient is a natural number. Here the
positive polynomials are exactly the image of `ℕ[A][M][σ]`; no finiteness of
the coefficient-variable set or the exponent monoid is needed. -/
theorem isPositive_principalCompletion_natPolynomial_iff
    (x : (ofIdeal (MvPolynomial.idealOfVars σ B)).completion) :
    (ofIdeal (MvPolynomial.idealOfVars σ B)).IsPositive
      ((MvPolynomial.map (σ := σ) natMap :
        MvPolynomial σ (AddMonoidAlgebra (MvPolynomial A ℕ) M) →+* MvPolynomial σ B).rangeS) x ↔
      ∀ (n : σ →₀ ℕ) (m : M) (a : A →₀ ℕ), ∃ c : ℕ,
        ((MvPowerSeries.coeff n (principalCompletionEquiv σ B x)).coeff m).coeff a = (c : ℚ) := by
  rw [isPositive_principalCompletion_iff]
  constructor
  · intro hx n m a
    obtain ⟨p, hp⟩ := hx n
    refine ⟨(p.coeff m).coeff a, ?_⟩
    rw [← hp, AddMonoidAlgebra.coeff_mapRingHom, MvPolynomial.coeff_map]
    rfl
  · intro hx n
    have hm : ∀ m, (MvPowerSeries.coeff n
        (principalCompletionEquiv σ B x)).coeff m ∈
        Set.range (MvPolynomial.map (σ := A) (Nat.castRingHom ℚ)) := by
      intro m
      apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
      intro c hc
      obtain ⟨a, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      obtain ⟨b, hb⟩ := hx n m a
      exact ⟨b, hb.symm⟩
    exact (Set.ext_iff.mp (AddMonoidAlgebra.range_map
      (MvPolynomial.map (σ := A) (Nat.castRingHom ℚ)).toAddMonoidHom) _).mpr hm

end Mei.AlgFiltration
