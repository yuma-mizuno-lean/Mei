/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.MonoidAlgebra.Filtration
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic

/-!
# Power series evaluated at a monomial of a filtered monoid algebra

Let `F` be a filtration of `R[M]` and `x` an element of the first completed ideal that is the
completion of the monomial `z^m`. Evaluating a power series `g = ∑ᵢ gᵢ Xⁱ` at `x` gives, at order
`k`, the class of `∑_{i ≤ k} gᵢ z^{i • m}`
(`TauCeti.AlgFiltration.projection_completedAeval_of_val_eq_toCompletion_single`); for instance
`1 + b X` gives the completion of `1 + b z^m`
(`TauCeti.AlgFiltration.completedAeval_one_add_C_mul_X_of_val_eq_toCompletion_single`).

Suppose the terms of `F` lie in the monomial ideals of an integral degree `δ` that is
nonnegative on `M` and positive on `m`. An element of the `k`-th monomial ideal has no
exponent of degree below `k` (`AddSubmonoid.coeff_eq_zero_of_mem_monoidAlgebraIdeal`), so the
finite projections determine the coefficients on the ray of `m`: if the completion of
`a ∈ R[M]` is the evaluation of `g` at `x`, then the coefficient of `z^{i • m}` in `a` is `gᵢ`
(`TauCeti.AlgFiltration.coeff_nsmul_of_toCompletion_eq_completedAeval`). Hence the evaluation of
`g` at `x` is the completion of an element of `R[M]` exactly when `g` is a polynomial
(`TauCeti.AlgFiltration.completedAeval_mem_range_toCompletion_iff`).
-/

public section

noncomputable section

open AddMonoidAlgebra

namespace AddSubmonoid

variable {M R : Type*} [AddCommMonoid M] [Semiring R] (P : AddSubmonoid M) {δ : M →+ ℤ}

/-- For a nonnegative degree, an element of the `k`-th monomial ideal has no exponent of degree
below `k`. -/
theorem coeff_eq_zero_of_mem_monoidAlgebraIdeal (hδ : ∀ n, 0 ≤ δ n) {k : ℕ} {f : R[M]}
    (hf : f ∈ P.monoidAlgebraIdeal δ k) {p : M} (hp : δ p < k) : f.coeff p = 0 := by
  by_contra h
  obtain ⟨n, -, hn, q, rfl⟩ :=
    (P.mem_monoidAlgebraIdeal_iff δ k f).mp hf p (Finsupp.mem_support_iff.mpr h)
  have hq := hδ q
  rw [map_add] at hp
  omega

end AddSubmonoid

namespace TauCeti.AlgFiltration

variable {R M : Type*} [CommRing R] [AddCommMonoid M] {F : AlgFiltration R[M]} {m : M}
  {x : F.completionIdeal 1}

/-- At order `k`, a power series `g` evaluated at the completion of `z^m` is the class of
`∑_{i ≤ k} gᵢ z^{i • m}`. -/
theorem projection_completedAeval_of_val_eq_toCompletion_single
    (hx : (x : F.completion) = F.toCompletion (single m 1)) (k : ℕ) (g : PowerSeries R) :
    F.projection k (F.completedAeval x g) =
      Ideal.Quotient.mk _
        (∑ i ∈ Finset.range (k + 1), single (i • m) (PowerSeries.coeff i g)) := by
  rw [F.projection_completedAeval_eq_sum, hx, projection_toCompletion, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, single_pow, one_pow, ← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul, smul_single,
    smul_eq_mul, mul_one]

/-- The linear polynomial `1 + b X` evaluated at the completion of `z^m` is the completion of
`1 + b z^m`. -/
theorem completedAeval_one_add_C_mul_X_of_val_eq_toCompletion_single
    (hx : (x : F.completion) = F.toCompletion (single m 1)) (b : R) :
    F.completedAeval x (1 + PowerSeries.C b * PowerSeries.X) = 1 + F.toCompletion (single m b) := by
  rw [map_add, map_one, map_mul, completedAeval_C, completedAeval_X, hx,
    ← toCompletion_algebraMap, ← map_mul, coe_algebraMap, Function.comp_apply, single_mul_single,
    zero_add, mul_one, Algebra.algebraMap_self, RingHom.id_apply]

variable {P : AddSubmonoid M} {δ : M →+ ℤ}

/-- Let the terms of `F` lie in the monomial ideals of a degree `δ` that is nonnegative on `M`
and positive on `m`. If the completion of `a ∈ R[M]` is a power series `g` evaluated at the
completion of `z^m`, then the coefficient of `z^{i • m}` in `a` is `gᵢ`. -/
theorem coeff_nsmul_of_toCompletion_eq_completedAeval
    (hF : ∀ k, F.ideal k ≤ P.monoidAlgebraIdeal δ k) (hδ : ∀ n, 0 ≤ δ n) (hm : 0 < δ m)
    (hx : (x : F.completion) = F.toCompletion (single m 1)) {a : R[M]} {g : PowerSeries R}
    (h : F.toCompletion a = F.completedAeval x g) (i : ℕ) :
    a.coeff (i • m) = PowerSeries.coeff i g := by
  have hk : ((δ (i • m)).toNat : ℤ) = i * δ m := by
    rw [Int.toNat_of_nonneg (hδ _), map_nsmul, nsmul_eq_mul]
  have hi : i ≤ (δ (i • m)).toNat := by
    have : (i : ℤ) ≤ i * δ m := le_mul_of_one_le_right (Int.natCast_nonneg i) hm
    omega
  have hmem := congrArg (F.projection (δ (i • m)).toNat) h
  rw [projection_toCompletion, projection_completedAeval_of_val_eq_toCompletion_single hx,
    Ideal.Quotient.eq] at hmem
  have h0 := P.coeff_eq_zero_of_mem_monoidAlgebraIdeal hδ (hF _ hmem) (p := i • m) (by omega)
  rw [coeff_sub, Finsupp.sub_apply, sub_eq_zero, coeff_sum, Finset.sum_apply',
    Finset.sum_eq_single_of_mem i (Finset.mem_range_succ_iff.mpr hi)] at h0
  · simpa using h0
  · intro j _ hj
    have hδj : δ (j • m) ≠ δ (i • m) := by
      simpa only [map_nsmul, nsmul_eq_mul, ne_eq, mul_eq_mul_right_iff, Nat.cast_inj, hm.ne',
        or_false] using hj
    rw [coeff_single, Finsupp.single_eq_of_ne' fun h => hδj (congrArg δ h)]

/-- Let the terms of `F` lie in the monomial ideals of a degree `δ` that is nonnegative on `M`
and positive on `m`. A power series evaluated at the completion of `z^m` is the completion of
an element of `R[M]` exactly when it is a polynomial. -/
theorem completedAeval_mem_range_toCompletion_iff
    (hF : ∀ k, F.ideal k ≤ P.monoidAlgebraIdeal δ k) (hδ : ∀ n, 0 ≤ δ n) (hm : 0 < δ m)
    (hx : (x : F.completion) = F.toCompletion (single m 1)) (g : PowerSeries R) :
    F.completedAeval x g ∈ Set.range F.toCompletion ↔
      ∃ p : Polynomial R, (p : PowerSeries R) = g := by
  constructor
  · rintro ⟨a, ha⟩
    have hinj : Function.Injective fun i : ℕ => i • m := fun i j hij => by
      simpa [hm.ne'] using congrArg δ hij
    have hfin : {i | PowerSeries.coeff i g ≠ 0}.Finite :=
      (a.coeff.support.finite_toSet.preimage hinj.injOn).subset fun i hi => by
        simpa [coeff_nsmul_of_toCompletion_eq_completedAeval hF hδ hm hx ha i] using hi
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine ⟨PowerSeries.trunc (N + 1) g, PowerSeries.ext fun i => ?_⟩
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left_iff, not_lt]
    exact fun hi => by_contra fun hg => (Nat.lt_succ_of_le (hN (Ne.symm hg))).not_ge hi
  · rintro ⟨p, rfl⟩
    refine ⟨Polynomial.aeval (single m 1) p, ?_⟩
    rw [completedAeval_coe, hx]
    simpa using (Polynomial.aeval_algHom_apply (F.toCompletionₐ (R := R)) (single m 1) p).symm

end TauCeti.AlgFiltration
