/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Integral basis coordinates in a scalar module

An additive map from an integral lattice into a module reconstructs each image
from the integral basis coordinates, cast into the target scalar ring. This lets
coordinate descriptions of lattice points be used in an ambient module.
-/

public section

namespace Module.Basis

/-- The image of a lattice vector is the linear combination of the basis images
with its integral coordinates cast into the target scalar ring. -/
@[simp]
theorem fintypeLinearCombination_repr_cast
    {ι N R V : Type*} [Fintype ι] [AddCommGroup N] [Ring R]
    [AddCommGroup V] [Module R V] (b : Basis ι ℤ N) (i : N →+ V) (n : N) :
    Fintype.linearCombination R (fun a => i (b a)) (fun a => (b.repr n a : R)) = i n := by
  simpa only [Fintype.linearCombination_apply, map_sum, map_zsmul,
    Int.cast_smul_eq_zsmul] using congrArg i (b.sum_repr n)

end Module.Basis
