/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Node.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Monomial normal forms for the nodal algebra

For any commutative ring `R` and `a : R`, the algebra `R[X,Y]/(XY-a)` has
the basis `X^n` for `n ≥ 0` and `Y^(n+1)` for `n ≥ 0`. Its two maps to the
Laurent polynomial ring `R[T;T⁻¹]`, given by `(X,Y) ↦ (T,aT⁻¹)` and `(aT⁻¹,T)`, are jointly
injective even when `a` is zero or a zero divisor. Nonnegative Laurent
coefficients in the first map and strictly positive coefficients in the second recover
the normal form. These formulas allow coefficients to be lifted from either
chamber of a slab without dividing by `a`.

We use Tau Ceti's `NodeAlgebra` and its universal map `NodeAlgebra.lift`,
and Mathlib's `LaurentPolynomial`, monoid-algebra coefficients and `Module.Basis.mk`.
The slab interpretation is that of Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, Definitions 3.1–3.3,
arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra LaurentPolynomial Module

variable {R : Type*} [CommRing R] (a : R)

/-- The Laurent chamber map sending `X` to `T` and `Y` to `a T⁻¹`. -/
def leftLaurentMap : NodeAlgebra R a →ₐ[R] R[T;T⁻¹] :=
  lift a (T 1) (C a * T (-1)) (by simp [← C_eq_algebraMap])

/-- The Laurent chamber map sending `X` to `a T⁻¹` and `Y` to `T`. -/
def rightLaurentMap : NodeAlgebra R a →ₐ[R] R[T;T⁻¹] :=
  lift a (C a * T (-1)) (T 1) (by simp [← C_eq_algebraMap])

@[simp]
theorem leftLaurentMap_coord_zero :
    leftLaurentMap a (coord a 0) = T 1 :=
  lift_coord_zero ..

@[simp]
theorem leftLaurentMap_coord_one :
    leftLaurentMap a (coord a 1) = C a * T (-1) :=
  lift_coord_one ..

@[simp]
theorem rightLaurentMap_coord_zero :
    rightLaurentMap a (coord a 0) = C a * T (-1) :=
  lift_coord_zero ..

@[simp]
theorem rightLaurentMap_coord_one :
    rightLaurentMap a (coord a 1) = T 1 :=
  lift_coord_one ..

private def normalMonomial : ℕ ⊕ ℕ → NodeAlgebra R a
  | .inl n => coord a 0 ^ n
  | .inr n => coord a 1 ^ (n + 1)

private theorem leftLaurentMap_normalMonomial (i : ℕ ⊕ ℕ) :
    leftLaurentMap a (normalMonomial a i) =
      match i with
      | .inl n => T n
      | .inr n => C (a ^ (n + 1)) * T (-(n + 1 : ℤ)) := by
  cases i <;> simp [normalMonomial, mul_pow]

private theorem rightLaurentMap_normalMonomial (i : ℕ ⊕ ℕ) :
    rightLaurentMap a (normalMonomial a i) =
      match i with
      | .inl n => C (a ^ n) * T (-(n : ℤ))
      | .inr n => T (n + 1 : ℤ) := by
  cases i <;> simp [normalMonomial, mul_pow]

private def normalCoeff (i : ℕ ⊕ ℕ) : NodeAlgebra R a →ₗ[R] R :=
  match i with
  | .inl n => ((Finsupp.lapply (n : ℤ)).comp (coeffLinearEquiv R).toLinearMap).comp
      (leftLaurentMap a).toLinearMap
  | .inr n => ((Finsupp.lapply (n + 1 : ℤ)).comp (coeffLinearEquiv R).toLinearMap).comp
      (rightLaurentMap a).toLinearMap

private theorem normalCoeff_normalMonomial (i j : ℕ ⊕ ℕ) :
    normalCoeff a i (normalMonomial a j) = if j = i then 1 else 0 := by
  cases i with
  | inl n =>
    cases j with
    | inl m => simp [normalCoeff, leftLaurentMap_normalMonomial, eq_comm]
    | inr m =>
      simp [normalCoeff, leftLaurentMap_normalMonomial, -map_pow, ← single_eq_C_mul_T,
        Finsupp.single_apply]
      omega
  | inr n =>
    cases j with
    | inl m =>
      simp [normalCoeff, rightLaurentMap_normalMonomial, -map_pow, ← single_eq_C_mul_T,
        Finsupp.single_apply]
      omega
    | inr m => simp [normalCoeff, rightLaurentMap_normalMonomial, eq_comm]

private theorem linearIndependent_normalMonomial : LinearIndependent R (normalMonomial a) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (normalMonomial a) (normalCoeff a)
  · intro i j hij
    simp [normalCoeff_normalMonomial, hij.symm]
  · intro i
    simp [normalCoeff_normalMonomial]

private theorem span_normalMonomial :
    ⊤ ≤ Submodule.span R (Set.range (normalMonomial a)) := by
  let S := Submodule.span R (Set.range (normalMonomial a))
  have hx (n : ℕ) : coord a 0 ^ n ∈ S :=
    Submodule.subset_span ⟨.inl n, rfl⟩
  have hy (n : ℕ) : coord a 1 ^ n ∈ S := by
    cases n with
    | zero => simpa using hx 0
    | succ n => exact Submodule.subset_span ⟨.inr n, rfl⟩
  have hmul (i : Fin 2) {z : NodeAlgebra R a} (hz : z ∈ S) :
      z * coord a i ∈ S := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      cases j with
      | inl n =>
        fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
        · simpa [normalMonomial, ← pow_succ] using hx (n + 1)
        · cases n with
          | zero => simpa [normalMonomial] using hy 1
          | succ n =>
            rw [normalMonomial, pow_succ, mul_assoc, coord_zero_mul_coord_one]
            simpa only [Algebra.smul_def, mul_comm] using S.smul_mem a (hx n)
      | inr n =>
        fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
        · have he : normalMonomial a (.inr n) * coord a 0 = a • coord a 1 ^ n := by
            simp only [normalMonomial, Algebra.smul_def, pow_succ]
            calc
              _ = coord a 1 ^ n * (coord a 0 * coord a 1) := by ring
              _ = _ := by rw [coord_zero_mul_coord_one, mul_comm]
          rw [he]
          exact S.smul_mem a (hy n)
        · simpa [normalMonomial, ← pow_succ] using hy (n + 2)
    | zero => simp
    | add x y _ _ hx hy => simpa [add_mul] using S.add_mem hx hy
    | smul r x _ hx => simpa [smul_mul_assoc] using S.smul_mem r hx
  intro z hz
  clear hz
  obtain ⟨p, rfl⟩ := mk_surjective a z
  induction p using MvPolynomial.induction_on with
  | C r => simpa [Algebra.smul_def] using S.smul_mem r (hx 0)
  | add p q hp hq => simpa using S.add_mem hp hq
  | mul_X p i hp => simpa using hmul i hp

/-- The monomial normal-form basis of `R[X,Y]/(XY-a)`: nonnegative powers
of `X`, together with strictly positive powers of `Y`. No regularity of `a`
is required. -/
def normalFormBasis : Basis (ℕ ⊕ ℕ) R (NodeAlgebra R a) :=
  Basis.mk (linearIndependent_normalMonomial a) (span_normalMonomial a)

@[simp]
theorem normalFormBasis_inl (n : ℕ) :
    normalFormBasis a (.inl n) = coord a 0 ^ n :=
  Basis.mk_apply _ _ _

@[simp]
theorem normalFormBasis_inr (n : ℕ) :
    normalFormBasis a (.inr n) = coord a 1 ^ (n + 1) :=
  Basis.mk_apply _ _ _

private theorem normalFormBasis_repr_eq (z : NodeAlgebra R a) (i : ℕ ⊕ ℕ) :
    (normalFormBasis a).repr z i = normalCoeff a i z := by
  refine (normalFormBasis a).repr_apply_eq (fun z i => normalCoeff a i z) ?_ ?_ ?_ z i
  · intro x y
    ext j
    exact map_add (normalCoeff a j) x y
  · intro r x
    ext j
    exact map_smul (normalCoeff a j) r x
  · intro j
    ext k
    have hj : normalFormBasis a j = normalMonomial a j := Basis.mk_apply _ _ _
    rw [hj, normalCoeff_normalMonomial]
    simp [Finsupp.single_apply]

/-- The first chamber's coefficient of `T^n` recovers the coefficient of `X^n`. -/
@[simp]
theorem normalFormBasis_repr_inl (z : NodeAlgebra R a) (n : ℕ) :
    (normalFormBasis a).repr z (.inl n) = (leftLaurentMap a z).coeff (n : ℤ) := by
  simpa [normalCoeff] using normalFormBasis_repr_eq a z (.inl n)

/-- The second chamber's coefficient of `T^(n+1)` recovers the coefficient
of `Y^(n+1)`. -/
@[simp]
theorem normalFormBasis_repr_inr (z : NodeAlgebra R a) (n : ℕ) :
    (normalFormBasis a).repr z (.inr n) =
      (rightLaurentMap a z).coeff (n + 1 : ℤ) := by
  simpa [normalCoeff] using normalFormBasis_repr_eq a z (.inr n)

/-- The two Laurent chamber maps are jointly injective, including at singular
and nonreduced values of the nodal parameter. -/
theorem laurentMaps_jointly_injective :
    Function.Injective (fun z : NodeAlgebra R a => (leftLaurentMap a z, rightLaurentMap a z)) := by
  intro x y h
  obtain ⟨hl, hr⟩ := Prod.mk.inj h
  apply (normalFormBasis a).repr.injective
  ext i
  cases i with
  | inl n => simp only [normalFormBasis_repr_inl, hl]
  | inr n => simp only [normalFormBasis_repr_inr, hr]

end Mei.NodeAlgebra
