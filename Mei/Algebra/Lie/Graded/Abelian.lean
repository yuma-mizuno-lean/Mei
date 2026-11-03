/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mei.Algebra.Lie.Abelian
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Gradings of finitely supported abelian Lie algebras

The abelian Lie algebra `Mei.AbelianLie (S →₀ R)` on the free module with basis `S` is graded by
any degree function `deg : S → Γ`: the piece of degree `n` is spanned by the basis vectors
`Finsupp.single s 1` with `deg s = n`. The pieces form an internal decomposition, and the zero
bracket is trivially homogeneous. A piece is zero when no basis vector has that degree.

This is the model of an abelian Lie algebra with independent generators in prescribed degrees,
for instance one generator in each positive degree.
-/

public section

noncomputable section

namespace Mei.AbelianLie

variable {S Γ : Type*} (R : Type*) [CommRing R] (deg : S → Γ)

/-- The standard basis of the abelian Lie algebra on the free module with basis `S`. -/
def basis : Module.Basis S R (AbelianLie (S →₀ R)) :=
  Finsupp.basisSingleOne.map (linearEquiv R).symm

/-- The grading of `AbelianLie (S →₀ R)` whose degree-`n` piece is spanned by the basis vectors
of degree `n`. -/
def grading (n : Γ) : Submodule R (AbelianLie (S →₀ R)) :=
  ⨆ s, ⨆ _ : deg s = n, R ∙ basis R s

variable {R deg}

/-- The basis vector `basis R s` lies in the piece of degree `deg s`. -/
theorem basis_mem_grading (s : S) : basis R s ∈ grading R deg (deg s) :=
  Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem rfl (Submodule.mem_span_singleton_self _))

/-- The piece of degree `n` is zero when no `s` has `deg s = n`. -/
theorem grading_eq_bot_of_forall_ne {n : Γ} (h : ∀ s, deg s ≠ n) : grading R deg n = ⊥ := by
  simp [grading, h]

variable (R deg)

/-- The pieces of `grading R deg` form an internal decomposition. -/
theorem isInternal_grading [DecidableEq Γ] : DirectSum.IsInternal (grading R deg) := by
  classical
  have h : DirectSum.IsInternal (fun s : S => R ∙ basis R s) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (basis R).linearIndependent.iSupIndep_span_singleton
      (by rw [← Submodule.span_range_eq_iSup, (basis R).span_eq])
  exact h.iSup_fiber deg

/-- The zero bracket is homogeneous, so the pieces of `grading R deg` form a Lie grading. -/
instance [AddCommMonoid Γ] [DecidableEq Γ] : GradedLieAlgebra (grading R deg) where
  toDecomposition := (isInternal_grading R deg).chooseDecomposition
  bracket_mem := by simp

end Mei.AbelianLie

end
