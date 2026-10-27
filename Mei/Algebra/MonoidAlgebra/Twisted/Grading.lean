/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The exponent grading of a twisted monoid algebra

A normalized factor set changes the scalar in a product of monomials but preserves
its exponent. Thus a twisted algebra on an additive monoid has its usual exponent
grading, with each homogeneous piece the span of one monomial. This grading allows
degree filtrations and completions of twisted coefficient algebras.

We use `TauCeti.TwistedMonoidAlgebra.basis` and `of_mul_of` for the decomposition
and multiplication, respectively. No nontriviality assumption on the scalar
ring is needed.
-/

public section

noncomputable section

namespace TauCeti.TwistedMonoidAlgebra

section Semiring

variable {M : Type*} (R : Type*) [CommSemiring R] [AddMonoid M]
  (α : Multiplicative M → Multiplicative M → Rˣ) [IsFactorSet α]

/-- The degree-`m` piece is the scalar span of the twisted monomial at `m`. -/
def grade (m : M) : Submodule R (twistedMonoidAlgebra R (Multiplicative M) α) :=
  R ∙ of (Multiplicative.ofAdd m)

/-- Homogeneity is exactly being a scalar multiple of the indicated monomial. -/
theorem mem_grade_iff (m : M) (x : twistedMonoidAlgebra R (Multiplicative M) α) :
    x ∈ grade R α m ↔ ∃ r : R, r • of (Multiplicative.ofAdd m) = x :=
  Submodule.mem_span_singleton

/-- A monomial belongs to its exponent's homogeneous piece. -/
theorem of_mem_grade (m : M) : of (Multiplicative.ofAdd m) ∈ grade R α m :=
  Submodule.mem_span_singleton_self _

instance instGradedMonoidGrade : SetLike.GradedMonoid (grade R α) where
  one_mem := by
    simpa using of_mem_grade R α (0 : M)
  mul_mem i j x y hx hy := by
    obtain ⟨r, rfl⟩ := (mem_grade_iff R α i x).mp hx
    obtain ⟨s, rfl⟩ := (mem_grade_iff R α j y).mp hy
    rw [smul_mul_smul_comm, of_mul_of]
    exact (grade R α (i + j)).smul_mem _
      ((grade R α (i + j)).smul_mem _ (of_mem_grade R α (i + j)))

end Semiring

variable {M : Type*} (R : Type*) [CommRing R] [AddMonoid M]
  (α : Multiplicative M → Multiplicative M → Rˣ) [IsFactorSet α]

/-- The monomial pieces give a direct-sum decomposition, also over the zero ring. -/
theorem isInternal_grade [DecidableEq M] : DirectSum.IsInternal (grade R α) := by
  let b := (basis R (Multiplicative M) α).reindex Multiplicative.toAdd
  have hg : grade R α = fun m => R ∙ b m := by
    funext m
    simp only [grade, b, Module.Basis.reindex_apply, basis_apply]
    rfl
  rw [hg]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (R := R)
    (A := fun m => R ∙ b m)
  · exact b.linearIndependent.iSupIndep_span_singleton
  · simpa only [Submodule.iSup_span, Set.iUnion_singleton_eq_range] using b.span_eq

instance instGradedAlgebraGrade [DecidableEq M] : GradedAlgebra (grade R α) :=
  (isInternal_grade R α).gradedAlgebra

/-- The homogeneous component of an element is its basis coefficient times the monomial. -/
theorem coe_decompose_grade [DecidableEq M]
    (x : twistedMonoidAlgebra R (Multiplicative M) α) (m : M) :
    (DirectSum.decompose (grade R α) x m : twistedMonoidAlgebra R (Multiplicative M) α) =
      (basis R (Multiplicative M) α).repr x (Multiplicative.ofAdd m) •
        of (Multiplicative.ofAdd m) := by
  induction x using DirectSum.Decomposition.inductionOn (grade R α) with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | @homogeneous j x =>
    obtain ⟨r, hr⟩ := (mem_grade_iff R α j x.val).mp x.property
    have hx := x.property
    rw [← hr] at hx ⊢
    by_cases hjm : j = m
    · subst m
      rw [DirectSum.decompose_of_mem_same (grade R α) hx]
      simp [← basis_apply]
    · rw [DirectSum.decompose_of_mem_ne (grade R α) hx hjm]
      simp [← basis_apply, Ne.symm hjm]

end TauCeti.TwistedMonoidAlgebra
