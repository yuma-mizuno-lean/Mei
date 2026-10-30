/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.RingTheory.Node.NormalForm
public import Mei.RingTheory.Node.ScalarTower
public import Mathlib.RingTheory.AlgebraTower

/-!
# Signed monomials of the nodal algebra

In `R[X,Y]/(XY-a)` the monomial normal forms are indexed by a single integer: the signed
monomial of `n ≤ 0` is `X^(-n)` and that of `n ≥ 0` is `Y^n`. They form an `R`-basis of the
nodal algebra, a reindexing of `Mei.NodeAlgebra.normalFormBasis`. A product of two signed
monomials is the signed monomial of the sum, multiplied by `a^r`, where `r` counts the pairs
`XY` that cancel: `r = (|n| + |m| - |n + m|) / 2`.

Over a Laurent polynomial ring `S[W, W⁻¹]`, the products `W^b` times a signed monomial form an
`S`-basis indexed by `ℤ × ℤ`, for every value of the nodal parameter. In particular the nodal
algebra is free, hence flat, over `S`. This is the normal form of the slab algebras of
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3 (arXiv:0808.2749v2), and of the
focus-focus singularity.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra LaurentPolynomial Module

section Signed

variable {R : Type*} [CommRing R] (a : R)

/-- The signed monomial of `n : ℤ` in `R[X,Y]/(XY-a)`: `X^(-n)` for `n ≤ 0` and `Y^n` for
`n ≥ 0`. -/
def signedMonomial (n : ℤ) : NodeAlgebra R a :=
  coord a 0 ^ (-n).toNat * coord a 1 ^ n.toNat

/-- The signed monomial of a natural number `n` is `Y^n`. -/
@[simp]
theorem signedMonomial_natCast (n : ℕ) : signedMonomial a n = coord a 1 ^ n := by
  simp [signedMonomial]

/-- The signed monomial of `-n`, for a natural number `n`, is `X^n`. -/
@[simp]
theorem signedMonomial_neg_natCast (n : ℕ) : signedMonomial a (-n) = coord a 0 ^ n := by
  simp [signedMonomial]

/-- The signed monomial of `0` is `1`. -/
@[simp]
theorem signedMonomial_zero : signedMonomial a 0 = 1 := by
  simpa using signedMonomial_natCast a 0

/-- On an incoming left weight, the Laurent image reads the scalar coefficient
without a factor of the nodal parameter. -/
theorem leftLaurentMap_smul_signedMonomial_of_nonpos (n : ℤ) (hn : n ≤ 0) (c : R) :
    leftLaurentMap a (c • signedMonomial a n) = AddMonoidAlgebra.single (-n) c := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hn)
  have he : n = -(d : ℤ) := by omega
  rw [he]
  simp [Algebra.smul_def, ← C_eq_algebraMap, C, T,
    AddMonoidAlgebra.single_mul_single, -single_eq_C_mul_T]

/-- On an incoming right weight, the Laurent image reads the scalar coefficient
without a factor of the nodal parameter. -/
theorem rightLaurentMap_smul_signedMonomial_of_nonneg (n : ℤ) (hn : 0 ≤ n) (c : R) :
    rightLaurentMap a (c • signedMonomial a n) = AddMonoidAlgebra.single n c := by
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  simp [Algebra.smul_def, ← C_eq_algebraMap, C, T,
    AddMonoidAlgebra.single_mul_single, -single_eq_C_mul_T]

/-- The product of two signed monomials is the signed monomial of the sum times `a^r`, where
`r = (|n| + |m| - |n + m|) / 2` is the number of cancelling pairs `XY = a`. -/
theorem signedMonomial_mul_signedMonomial (n m : ℤ) :
    signedMonomial a n * signedMonomial a m =
      algebraMap R (NodeAlgebra R a) a ^ ((n.natAbs + m.natAbs - (n + m).natAbs) / 2) *
        signedMonomial a (n + m) := by
  set r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
  have hX : (-n).toNat + (-m).toNat = r + (-(n + m)).toNat := by omega
  have hY : n.toNat + m.toNat = r + (n + m).toNat := by omega
  calc
    signedMonomial a n * signedMonomial a m =
        coord a 0 ^ ((-n).toNat + (-m).toNat) * coord a 1 ^ (n.toNat + m.toNat) := by
      simp only [signedMonomial]
      ring
    _ = (coord a 0 * coord a 1) ^ r * signedMonomial a (n + m) := by
      rw [hX, hY, signedMonomial]
      ring
    _ = _ := by rw [coord_zero_mul_coord_one]

/-- The equivalence `ℤ ≃ ℕ ⊕ ℕ` sending `-d` to `.inl d` and `d + 1` to `.inr d`, matching
signed monomials with the indices of `normalFormBasis`. -/
private def signedIndexEquiv : ℤ ≃ ℕ ⊕ ℕ :=
  (Equiv.neg ℤ).trans Equiv.intEquivNatSumNat

/-- The signed monomials form an `R`-basis of `R[X,Y]/(XY-a)`, for every `a`. -/
def signedMonomialBasis : Basis ℤ R (NodeAlgebra R a) :=
  (normalFormBasis a).reindex signedIndexEquiv.symm

@[simp]
theorem signedMonomialBasis_apply (n : ℤ) : signedMonomialBasis a n = signedMonomial a n := by
  obtain ⟨i, rfl⟩ := signedIndexEquiv.symm.surjective n
  rw [signedMonomialBasis, Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  -- `signedIndexEquiv.symm` sends `.inl d` to `-d` and `.inr d` to `d + 1` by definition.
  cases i with
  | inl d =>
    rw [show signedIndexEquiv.symm (.inl d) = -(d : ℤ) from rfl]
    simp
  | inr d =>
    rw [show signedIndexEquiv.symm (.inr d) = ((d + 1 : ℕ) : ℤ) from rfl,
      signedMonomial_natCast]
    simp

end Signed

section Laurent

open scoped Mei.NodeAlgebra

variable {S : Type*} [CommRing S] (a : S[T;T⁻¹])

/-- Over a Laurent polynomial ring `S[W, W⁻¹]`, the elements `W^b` times the signed monomial of
`n` form an `S`-basis of `S[W, W⁻¹][X,Y]/(XY-a)` indexed by `(n, b) : ℤ × ℤ`, for every `a`. -/
def laurentBasis : Basis (ℤ × ℤ) S (NodeAlgebra S[T;T⁻¹] a) :=
  (AddMonoidAlgebra.basis ℤ S).smulTower' (signedMonomialBasis a)

@[simp]
theorem laurentBasis_apply (n b : ℤ) :
    laurentBasis a (n, b) = (T b : S[T;T⁻¹]) • signedMonomial a n := by
  rw [laurentBasis, Basis.smulTower'_apply]
  simp only [AddMonoidAlgebra.basis_apply, signedMonomialBasis_apply]
  rw [single_eq_C_mul_T, map_one, one_mul]

/-- A nodal algebra over a Laurent polynomial ring `S[W, W⁻¹]` is free over `S`. -/
instance : Module.Free S (NodeAlgebra S[T;T⁻¹] a) :=
  .of_basis (laurentBasis a)

end Laurent

end Mei.NodeAlgebra
