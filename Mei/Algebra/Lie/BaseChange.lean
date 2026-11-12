/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Rational scalars on extended Lie algebras

When the coefficient algebra is a `ℚ`-algebra, its rational action on the left
tensor factor makes the scalar extension a rational Lie algebra. This retains
the canonical tensor-product module structure.

For any commutative `R`-algebra `S`, the map `x ↦ 1 ⊗ x` is an `R`-linear Lie homomorphism
`L → S ⊗[R] L` (`LieAlgebra.ExtendScalars.includeRight`).
-/

public section

open TensorProduct

namespace LieAlgebra.ExtendScalars

section Rat

variable {R S L : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ S] [LieRing L] [LieAlgebra R L]

/-- Rational scalars act on the left factor of an extended Lie algebra,
retaining its canonical tensor-product module structure. -/
@[instance_reducible]
noncomputable instance instRatLieAlgebra : LieAlgebra ℚ (S ⊗[R] L) where
  lie_smul q x y := by
    simpa only [IsScalarTower.algebraMap_smul] using lie_smul (algebraMap ℚ S q) x y

end Rat

section IncludeRight

variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [LieRing L] [LieAlgebra R L]

/-- The `R`-linear Lie homomorphism `x ↦ 1 ⊗ x` from `L` to its scalar extension. -/
def includeRight : L →ₗ⁅R⁆ S ⊗[R] L where
  toLinearMap := TensorProduct.mk R S L 1
  map_lie' {x y} := by simp [bracket_tmul]

variable {R S L}

/-- The inclusion sends `x` to `1 ⊗ x`. -/
@[simp]
theorem includeRight_apply (x : L) : includeRight R S L x = 1 ⊗ₜ x := (rfl)

end IncludeRight

end LieAlgebra.ExtendScalars
