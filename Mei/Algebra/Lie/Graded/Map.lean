/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded

/-!
# Images of graded Lie brackets

The images of homogeneous submodules under a Lie homomorphism still have a graded bracket.
No injectivity or surjectivity is required: this gives bracket compatibility for quotient
pieces as well as for the image of a graded Lie algebra.
-/

public section

namespace LieHom

variable {R L L' ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] [VAdd ι ι]

/-- A Lie homomorphism transports a graded bracket to the images of the homogeneous pieces.
This does not assert that the image pieces are independent. -/
theorem gradedBracket_map (f : L →ₗ⁅R⁆ L') (ℒ : ι → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (fun i ↦ (ℒ i).map f.toLinearMap)
      (fun i ↦ (ℒ i).map f.toLinearMap) := by
  constructor
  intro i j x y hx hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
  exact Submodule.mem_map.2
    ⟨⁅a, b⁆, SetLike.GradedBracket.bracket_mem ha hb, f.map_lie a b⟩

end LieHom
