/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.BaseChange
public import Mei.Algebra.PositiveDegrees.BaseChange
public import Mei.Algebra.Lie.Graded.Truncation
public import TauCeti.Algebra.Lie.BaseChange.Quotient
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Extension of scalars for graded Lie algebras and truncations

Extending each homogeneous piece gives a Lie grading on the scalar extension.
For positive gradings, degree ideals extend to degree ideals, and truncation
commutes with extension of scalars as a Lie algebra. No flatness, freeness, or
dimension hypothesis is imposed on either the pieces or the coefficient algebra.

The decomposition is Mathlib's `DirectSum.Decomposition.baseChange`; the
truncation comparison uses Tau Ceti's `LieIdeal.quotientBaseChangeEquiv`.
-/

public section

open TensorProduct

variable {N R S L : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [LieRing L] [LieAlgebra R L]

/-- Extension of scalars preserves homogeneous brackets. -/
instance SetLike.GradedBracket.baseChange [VAdd N N] (ℒ : N → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (fun n => (ℒ n).baseChange S) (fun n => (ℒ n).baseChange S) where
  bracket_mem := by
    intro i j x y hx hy
    rw [Submodule.baseChange_eq_span] at hx hy
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      ((ℒ (i +ᵥ j)).baseChange S) _ _
      (TensorProduct.curry (LieModule.toModuleHom S
        (S ⊗[R] L) (S ⊗[R] L)).toLinearMap) ?_ x y hx hy
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simpa using Submodule.tmul_mem_baseChange_of_mem (1 : S)
      (SetLike.GradedBracket.bracket_mem (ℒ := ℒ) (ℳ := ℒ) hu hv)

variable [AddCommMonoid N] [DecidableEq N] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

/-- The extended homogeneous pieces form a Lie grading on the scalar extension. -/
instance GradedLieAlgebra.baseChange :
    GradedLieAlgebra (fun n => (ℒ n).baseChange S) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

namespace Mei.PositiveDegrees

variable (d : PositiveDegrees N) [IsPositiveGrading d ℒ]

/-- Extending scalars commutes with the Lie ideal above a degree cutoff. -/
@[simp]
theorem degreeIdeal_baseChange (k : ℕ) :
    (d.degreeIdeal ℒ k).baseChange S =
      d.degreeIdeal (fun n => (ℒ n).baseChange S) k := by
  apply LieSubmodule.toSubmodule_injective
  simp only [LieSubmodule.coe_baseChange, degreeIdeal_toSubmodule, degreeSubmodule_baseChange]

/-- Truncation and extension of scalars commute as Lie algebras. -/
noncomputable def truncatedBaseChangeEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).baseChange S) k ≃ₗ⁅S⁆
      S ⊗[R] d.truncatedLie ℒ k :=
  Eq.rec (motive := fun J _ => ((S ⊗[R] L) ⧸ J) ≃ₗ⁅S⁆ S ⊗[R] d.truncatedLie ℒ k)
    ((d.degreeIdeal ℒ k).quotientBaseChangeEquiv S) (d.degreeIdeal_baseChange ℒ k)

/-- The comparison commutes with the scalar extension of the quotient projection. -/
@[simp]
theorem truncatedBaseChangeEquiv_mk (k : ℕ) (z : S ⊗[R] L) :
    d.truncatedBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk z) =
      LieHom.baseChange S (d.degreeIdeal ℒ k).mkQ z := by
  -- Eliminate the ideal equality before evaluating the transported equivalence.
  have eval (J : LieIdeal S (S ⊗[R] L)) (h : (d.degreeIdeal ℒ k).baseChange S = J) :
      (h ▸ (d.degreeIdeal ℒ k).quotientBaseChangeEquiv S)
          (LieSubmodule.Quotient.mk z) =
        LieHom.baseChange S (d.degreeIdeal ℒ k).mkQ z := by
    subst J
    exact (d.degreeIdeal ℒ k).quotientBaseChangeEquiv_mk S z
  exact eval _ (d.degreeIdeal_baseChange (S := S) ℒ k)

/-- The comparison sends the class of a pure tensor to the tensor of the class. -/
theorem truncatedBaseChangeEquiv_mk_tmul (k : ℕ) (s : S) (x : L) :
    d.truncatedBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k) := by
  simp only [truncatedBaseChangeEquiv_mk, LieHom.baseChange_tmul, LieIdeal.mkQ_apply]

/-- The inverse comparison sends a tensor of a class to the class of the tensor. -/
@[simp]
theorem truncatedBaseChangeEquiv_symm_tmul (k : ℕ) (s : S) (x : L) :
    (d.truncatedBaseChangeEquiv ℒ k).symm
        (s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k)) =
      LieSubmodule.Quotient.mk (s ⊗ₜ[R] x) :=
  (d.truncatedBaseChangeEquiv ℒ k).symm_apply_eq.mpr
    (d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x).symm

/-- The truncation comparison identifies each extended homogeneous piece. -/
theorem map_truncatedGrading_baseChange (k : ℕ) (n : N) :
    (d.truncatedGrading (fun n => (ℒ n).baseChange S) k n).map
        (d.truncatedBaseChangeEquiv ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).baseChange S := by
  have square : (d.truncatedBaseChangeEquiv ℒ k).toLinearMap.comp
      (d.degreeIdeal (fun n => (ℒ n).baseChange S) k).toSubmodule.mkQ =
        (d.degreeIdeal ℒ k).toSubmodule.mkQ.baseChange S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LieHom.coe_toLinearMap, LieEquiv.coe_coe]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x
  rw [truncatedGrading_eq, ← Submodule.map_comp, square, truncatedGrading_eq,
    Submodule.baseChange_map]

end Mei.PositiveDegrees
