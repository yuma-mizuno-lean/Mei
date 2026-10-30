/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mei.Algebra.MonoidAlgebra.Monomial
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Components, currying and coefficient maps of monoid algebras

The homogeneous component in the exponent grading is the corresponding coefficient
times its monomial. Currying a product exponent preserves its first homogeneous
degree, and its coefficients retain both exponent coordinates. These formulas
relate full exponent gradings to coarser gradings over a monoid coefficient algebra.

Changing coefficients also preserves the pieces of any grading given by a degree
function on monomials, including when coefficients vanish under the map.

We use Mathlib's `AddMonoidAlgebra.grade` and `curryAlgEquiv`.
-/

public section

noncomputable section

namespace AddMonoidAlgebra

section CoefficientChange

variable {K R S M ι : Type*} [CommSemiring K] [CommSemiring R] [CommSemiring S]
  [Algebra K R] [Algebra K S] [AddMonoid M]

/-- Coefficient change preserves homogeneous support for an arbitrary degree function. -/
theorem mapAlgHom_mem_gradeBy (φ : R →ₐ[K] S) {f : M → ι} {i : ι} {u : R[M]}
    (hu : u ∈ gradeBy R f i) : mapAlgHom M φ u ∈ gradeBy S f i := by
  exact fun m hm => hu m (Finsupp.support_mapRange (hf := φ.map_zero) hm)

end CoefficientChange

section CurryCoefficientChange

variable {K R S M ι : Type*} [CommSemiring K] [Semiring R] [Semiring S]
  [Algebra K R] [Algebra K S] [AddMonoid M]

/-- Changing coefficients commutes with currying the two exponent coordinates. -/
@[simp]
theorem curryAlgEquiv_mapAlgHom [AddMonoid ι] (x : R[M × ι]) (φ : R →ₐ[K] S) :
    curryAlgEquiv K (mapAlgHom (M × ι) φ x) =
      mapAlgHom M (mapAlgHom ι φ) (curryAlgEquiv K x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p r =>
    rcases p with ⟨m, n⟩
    simp

end CurryCoefficientChange

open scoped AlgebraMonoidAlgebra in
/-- After currying, scalar coefficient change is coefficient change over the
corresponding monoid algebra. -/
@[simp]
theorem curryAlgEquiv_mapAlgHom_ofId {R S M N : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid M] [AddMonoid N]
    (x : R[N × M]) :
    curryAlgEquiv S (mapAlgHom (N × M) (Algebra.ofId R S) x) =
      mapAlgHom N (Algebra.ofId R[M] S[M]) (curryAlgEquiv R x) := by
  -- Currying has the same underlying ring equivalence for either scalar ring.
  refine (curryAlgEquiv_mapAlgHom x (Algebra.ofId R S)).trans ?_
  ext n m
  simp only [coeff_mapAlgHom, Algebra.ofId_apply, algebraMap_def, coeff_mapRingHom]

variable {R M N : Type*} [CommSemiring R] [AddMonoid M]

/-- A component in the exponent grading is a single monomial. -/
@[simp]
theorem coe_decompose_grade [DecidableEq M] (x : R[M]) (m : M) :
    (DirectSum.decompose (grade R) x m : R[M]) = single m (x.coeff m) := by
  -- The standard basis is defined by the coefficient equivalence.
  have hrepr : (basis M R).repr x m = x.coeff m := rfl
  simpa only [Mei.AddMonoidAlgebra.monomialPresentation_basis, hrepr,
    basis_apply, smul_single, smul_eq_mul, mul_one] using
    (Mei.AddMonoidAlgebra.monomialPresentation (R := R) (Γ := M)).coe_decompose x m

/-- Uncurrying reads the two nested coefficients at the product exponent. -/
@[simp]
theorem coeff_curryAlgEquiv_symm [AddMonoid N] (x : R[N][M]) (m : M) (n : N) :
    ((curryAlgEquiv R).symm x).coeff (m, n) = (x.coeff m).coeff n := (rfl)

/-- A fully homogeneous monomial is homogeneous in the outer degree after currying. -/
theorem curryAlgEquiv_mem_grade [AddCommMonoid N] (p : M × N) (x : R[M × N])
    (hx : x ∈ grade R p) :
    curryAlgEquiv R x ∈ grade R[N] p.1 := by
  rcases p with ⟨m, n⟩
  obtain ⟨c, rfl⟩ := (mem_grade_iff' R (m, n) x).mp hx
  simpa only [lsingle_apply, curryAlgEquiv_single] using single_mem_grade m (single n c)

/-- Currying a homogeneous element retains its tangential monomial coefficient. -/
theorem coeff_curryAlgEquiv_of_mem_grade [AddMonoid N] (p : M × N)
    (x : R[M × N]) (hx : x ∈ grade R p) :
    (curryAlgEquiv R x).coeff p.1 = single p.2 (x.coeff p) := by
  rcases p with ⟨m, n⟩
  obtain ⟨c, rfl⟩ := (mem_grade_iff' R (m, n) x).mp hx
  simp [lsingle_apply]

end AddMonoidAlgebra
