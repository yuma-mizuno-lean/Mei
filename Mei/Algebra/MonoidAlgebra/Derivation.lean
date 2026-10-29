/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.Derivation.Lie

/-!
# Monomial logarithmic derivations

For an additive character `m : M →+ R`, the monomial logarithmic derivation
`monomialDerivation n m` sends `r z^p` to `r m(p) z^(n+p)`. It is linear in
the character, shifts the standard monoid-algebra grading by `n`, and has
commutator character `m(n') m' - m'(n) m` in degree `n + n'`.
Characters annihilating their own degrees remain tangent under this bracket.
These are the generator and bracket computations for logarithmic vector fields
on a torus and their restrictions to monoid algebras.

The construction uses `AddMonoidAlgebra.basis.constr` and Mathlib's Lie algebra
of derivations. The logarithmic-vector-field formula follows Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i), arXiv:1503.06183v5. No positivity, rational coefficients or lattice
freeness is needed for these finite algebraic computations.
-/

public section

noncomputable section

open AddMonoidAlgebra

namespace Mei.AddMonoidAlgebra

variable {R M : Type*} [AddCommMonoid M]

section Semiring

variable [CommSemiring R]

private def monomialLinearMap (n : M) (m : M →+ R) : R[M] →ₗ[R] R[M] :=
  (basis M R).constr R fun p => single (n + p) (m p)

private theorem monomialLinearMap_single (n : M) (m : M →+ R) (p : M) (r : R) :
    monomialLinearMap n m (single p r) = single (n + p) (r * m p) := by
  have h : monomialLinearMap n m (single p 1) = single (n + p) (m p) := by
    exact (basis M R).constr_basis R (fun p => single (n + p) (m p)) p
  calc
    _ = monomialLinearMap n m (r • single p 1) := by simp
    _ = r • monomialLinearMap n m (single p 1) := map_smul _ _ _
    _ = _ := by rw [h]; simp

private theorem monomialLinearMap_leibniz (n : M) (m : M →+ R) (a b : R[M]) :
    monomialLinearMap n m (a * b) =
      a • monomialLinearMap n m b + b • monomialLinearMap n m a := by
  induction a using induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [add_mul, map_add, ha, ha', smul_eq_mul]
    ring
  | single p r =>
    induction b using induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [mul_add, map_add, hb, hb', smul_eq_mul]
      ring
    | single q s =>
      simp only [single_mul_single, monomialLinearMap_single, smul_eq_mul, map_add,
        add_left_comm, add_comm, ← single_add]
      congr 1
      ring

/-- The degree-`n` logarithmic derivation with additive character `m`, linear
in `m`. On a monomial it is `r z^p ↦ r m(p) z^(n+p)`. -/
def monomialDerivation (n : M) : (M →+ R) →ₗ[R] Derivation R R[M] R[M] where
  toFun m :=
    { monomialLinearMap n m with
      map_one_eq_zero' := by simp [one_def, monomialLinearMap_single]
      leibniz' := monomialLinearMap_leibniz n m }
  map_add' m m' := by
    apply Derivation.ext
    intro a
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => simp_all; abel
    | single p r =>
      simp [monomialLinearMap_single, mul_add, single_add]
  map_smul' c m := by
    apply Derivation.ext
    intro a
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => simp_all
    | single p r =>
      simp [monomialLinearMap_single, mul_left_comm]

/-- The characteristic monomial formula for logarithmic derivations. -/
@[simp]
theorem monomialDerivation_single (n : M) (m : M →+ R) (p : M) (r : R) :
    monomialDerivation n m (single p r) = single (n + p) (r * m p) :=
  monomialLinearMap_single n m p r

/-- A degree-`n` logarithmic derivation is the multiple of the degree-zero weight
derivation by the monomial `z^n`. -/
theorem monomialDerivation_eq_single_smul (n : M) (m : M →+ R) :
    monomialDerivation n m = (single n 1 : R[M]) • monomialDerivation 0 m := by
  apply Derivation.ext
  intro a
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp_all [mul_add]
  | single p r => simp [single_mul_single]

/-- A homogeneous logarithmic derivation uniquely determines its character,
even over a coefficient ring with zero divisors. -/
theorem monomialDerivation_injective (n : M) :
    Function.Injective (monomialDerivation (R := R) n) := by
  intro m m' he
  ext p
  have hp := congrArg (fun D : Derivation R R[M] R[M] => D (single p 1)) he
  simpa using hp

/-- Logarithmic derivations shift homogeneous monomials by their degree. -/
theorem monomialDerivation_mem_grade (n : M) (m : M →+ R) {p : M} {a : R[M]}
    (ha : a ∈ grade R p) : monomialDerivation n m a ∈ grade R (n + p) := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff' R p a).mp ha
  simpa using single_mem_grade (n + p) (r * m p)

/-- Homogeneous logarithmic vector fields tangent to their degree: the
characters `m` satisfy `m n = 0`. This is a submodule of actual derivations,
without a choice of presentation for a vector field. -/
def tangentMonomialDerivations (n : M) : Submodule R (Derivation R R[M] R[M]) where
  carrier := {D | ∃ m : M →+ R, m n = 0 ∧ monomialDerivation n m = D}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro D E ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', by simp [hm, hm'], by simp⟩
  smul_mem' := by
    rintro c D ⟨m, hm, rfl⟩
    exact ⟨c • m, by simp [hm], by simp⟩

/-- Membership is equivalent to a monomial expression whose character
annihilates the degree. -/
theorem mem_tangentMonomialDerivations_iff (n : M) (D : Derivation R R[M] R[M]) :
    D ∈ tangentMonomialDerivations n ↔
      ∃ m : M →+ R, m n = 0 ∧ monomialDerivation n m = D := Iff.rfl

/-- Tangency of a monomial logarithmic derivation is exactly tangency of
its character. -/
@[simp]
theorem monomialDerivation_mem_tangentMonomialDerivations_iff (n : M) (m : M →+ R) :
    monomialDerivation n m ∈ tangentMonomialDerivations n ↔ m n = 0 := by
  rw [mem_tangentMonomialDerivations_iff]
  constructor
  · rintro ⟨m', hm', he⟩
    exact (monomialDerivation_injective n he) ▸ hm'
  · exact fun hm => ⟨m, hm, rfl⟩

end Semiring

section Ring

variable [CommRing R]

/-- The commutator of monomial logarithmic derivations is again monomial,
with the usual logarithmic-vector-field character. -/
theorem lie_monomialDerivation (n n' : M) (m m' : M →+ R) :
    ⁅monomialDerivation n m, monomialDerivation n' m'⁆ =
      monomialDerivation (n + n') (m n' • m' - m' n • m) := by
  apply Derivation.ext
  intro a
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp_all; abel
  | single p r =>
    simp only [Derivation.commutator_apply, monomialDerivation_single, map_add,
      AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul,
      add_assoc, add_left_comm n' n p, ← single_sub]
    congr 1
    ring

/-- The bracket of tangent logarithmic vector fields is tangent in the sum
degree. In particular, these homogeneous submodules are closed under the
degree-additive Lie bracket. -/
theorem lie_mem_tangentMonomialDerivations {n n' : M} {D E : Derivation R R[M] R[M]}
    (hD : D ∈ tangentMonomialDerivations n) (hE : E ∈ tangentMonomialDerivations n') :
    ⁅D, E⁆ ∈ tangentMonomialDerivations (n + n') := by
  obtain ⟨m, hm, rfl⟩ := (mem_tangentMonomialDerivations_iff n D).mp hD
  obtain ⟨m', hm', rfl⟩ := (mem_tangentMonomialDerivations_iff n' E).mp hE
  rw [lie_monomialDerivation, monomialDerivation_mem_tangentMonomialDerivations_iff]
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, map_add, hm, hm',
    smul_eq_mul]
  ring

end Ring

end Mei.AddMonoidAlgebra
