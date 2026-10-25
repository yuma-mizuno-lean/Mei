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
-/

public section

open TensorProduct

namespace LieAlgebra.ExtendScalars

variable {R S L : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ S] [LieRing L] [LieAlgebra R L]

/-- Rational scalars act on the left factor of an extended Lie algebra,
retaining its canonical tensor-product module structure. -/
@[instance_reducible]
noncomputable instance instRatLieAlgebra : LieAlgebra ℚ (S ⊗[R] L) where
  lie_smul q x y := by
    simpa only [IsScalarTower.algebraMap_smul] using lie_smul (algebraMap ℚ S q) x y

end LieAlgebra.ExtendScalars
