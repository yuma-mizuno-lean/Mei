/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded

/-!
# Pulling back graded brackets

The inverse images of homogeneous pieces under a Lie homomorphism are compatible
with the bracket. This requires neither injectivity nor an internal direct-sum
decomposition; those extra conditions enter when constructing a Lie grading on a
homogeneous subalgebra.
-/

public section

namespace LieHom

variable {ι R L L' : Type*} [VAdd ι ι]
  [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- The inverse images of pieces with a graded bracket have a graded bracket. -/
instance instGradedBracketComap (f : L →ₗ⁅R⁆ L') (ℒ : ι → Submodule R L')
    [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (fun i => (ℒ i).comap f.toLinearMap)
      (fun i => (ℒ i).comap f.toLinearMap) where
  bracket_mem := by
    intro i j x y hx hy
    rw [Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie]
    exact SetLike.GradedBracket.bracket_mem hx hy

end LieHom
