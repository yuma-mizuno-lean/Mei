/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.BaseChange
public import Mei.Algebra.DirectSum.BaseChange
public import Mei.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.Lie.Quotient.Map
public import TauCeti.Algebra.Lie.BaseChange.Quotient

/-!
# Scalar extension of graded Lie algebras

Extending scalars preserves graded brackets, hence internal Lie gradings and
positive Lie gradings. Degree ideals commute with scalar extension, and
`truncatedBaseChangeEquiv` identifies truncating after extension with extending
the original truncation. It uses Tau Ceti's `LieIdeal.quotientBaseChangeEquiv`.

The underlying module decomposition is Mathlib's
`DirectSum.Decomposition.baseChange`. No flatness or freeness is required:
homogeneous pieces are already direct summands before extending scalars.
-/

public section

open scoped TensorProduct

variable {R S L M ι κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L]

/-- Scalar extension preserves a graded bracket action, independently of any decomposition. -/
instance SetLike.GradedBracket.baseChange [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [VAdd ι κ]
    (ℒ : ι → Submodule R L) (ℳ : κ → Submodule R M)
    [SetLike.GradedBracket ℒ ℳ] :
    SetLike.GradedBracket (fun i => (ℒ i).baseChange S)
      (fun j => (ℳ j).baseChange S) where
  bracket_mem := by
    intro i j x y hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      induction y using TensorProduct.inductionOn with
      | tmul t y =>
        simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
          LieAlgebra.ExtendScalars.bracket_tmul] using
          Submodule.tmul_mem_baseChange_of_mem (s * t)
            (SetLike.GradedBracket.bracket_mem x.property y.property)
      | add y z hy hz =>
        rw [map_add, lie_add]
        exact Submodule.add_mem _ hy hz
    | add x z hx hz =>
      rw [map_add, add_lie ((ℒ i).subtype.baseChange S x)
        ((ℒ i).subtype.baseChange S z) ((ℳ j).subtype.baseChange S y)]
      exact Submodule.add_mem _ hx hz

/-- A scalar-extended Lie algebra is internally graded by its base-changed pieces. -/
noncomputable instance GradedLieAlgebra.baseChange [DecidableEq ι] [AddCommMonoid ι]
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (fun i => (ℒ i).baseChange S) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

/-- Scalar extension preserves the grading of a representation of a graded Lie algebra. -/
instance GradedLieModule.baseChange [DecidableEq ι] [AddCommMonoid ι]
    [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]
    (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ] [GradedLieModule ℒ ℳ] :
    GradedLieModule (fun i => (ℒ i).baseChange S) (fun j => (ℳ j).baseChange S) where
  toGradedBracket := inferInstance

namespace Mei.PositiveDegrees

variable [DecidableEq ι] [AddCommMonoid ι]
  (d : Mei.PositiveDegrees ι) (ℒ : ι → Submodule R L)
  [GradedLieAlgebra ℒ] [Mei.IsPositiveGrading d ℒ]

/-- The degree ideal after scalar extension is the extension of the original degree ideal. -/
@[simp]
theorem degreeIdeal_baseChange (k : ℕ) :
    d.degreeIdeal (fun i => (ℒ i).baseChange S) k = (d.degreeIdeal ℒ k).baseChange S := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Finite degree truncations commute with arbitrary extension of the coefficient ring. -/
noncomputable def truncatedBaseChangeEquiv (k : ℕ) :
    d.truncatedLie (fun i => (ℒ i).baseChange S) k ≃ₗ⁅S⁆ S ⊗[R] d.truncatedLie ℒ k :=
  (LieIdeal.quotEquivOfEq _ _ (d.degreeIdeal_baseChange ℒ k)).trans
    (LieIdeal.quotientBaseChangeEquiv S (d.degreeIdeal ℒ k))

/-- The truncation comparison sends the class of a pure tensor to the tensor of its class. -/
@[simp]
theorem truncatedBaseChangeEquiv_mk_tmul (k : ℕ) (s : S) (x : L) :
    d.truncatedBaseChangeEquiv ℒ k (LieSubmodule.Quotient.mk (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k) := by
  simp [truncatedBaseChangeEquiv]

/-- The inverse truncation comparison also preserves pure-tensor representatives. -/
@[simp]
theorem truncatedBaseChangeEquiv_symm_tmul_mk (k : ℕ) (s : S) (x : L) :
    (d.truncatedBaseChangeEquiv (S := S) ℒ k).symm
      (s ⊗ₜ[R] (LieSubmodule.Quotient.mk x : d.truncatedLie ℒ k)) =
        LieSubmodule.Quotient.mk (s ⊗ₜ[R] x) :=
  (d.truncatedBaseChangeEquiv ℒ k).symm_apply_eq.mpr
    (d.truncatedBaseChangeEquiv_mk_tmul ℒ k s x).symm

end Mei.PositiveDegrees
