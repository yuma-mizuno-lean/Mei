/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Components and currying of monoid algebras

The homogeneous component in the exponent grading is the corresponding coefficient
times its monomial. Currying a product exponent preserves its first homogeneous
degree, and its coefficients retain both exponent coordinates. These formulas
relate full exponent gradings to coarser gradings over a monoid coefficient algebra.

We use Mathlib's `AddMonoidAlgebra.grade` and `curryAlgEquiv`.
-/

public section

noncomputable section

namespace AddMonoidAlgebra

variable {R M N : Type*} [CommSemiring R] [AddMonoid M]

/-- A component in the exponent grading is a single monomial. -/
@[simp]
theorem coe_decompose_grade [DecidableEq M] (x : R[M]) (m : M) :
    (DirectSum.decompose (grade R) x m : R[M]) = single m (x.coeff m) := by
  induction x using DirectSum.Decomposition.inductionOn (grade R : M → Submodule R R[M]) with
  | zero => simp
  | add x y hx hy => simp [hx, hy, single_add]
  | @homogeneous j x =>
    obtain ⟨c, hc⟩ := (mem_grade_iff' R j x.val).mp x.property
    rw [← hc, lsingle_apply, grade.decompose_single]
    by_cases h : j = m
    · subst m; simp
    · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), Ne.symm h]

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
