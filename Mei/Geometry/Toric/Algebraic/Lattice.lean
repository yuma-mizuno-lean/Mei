/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Scalar compatibility of real lattice characters

Real extension sends integer multiples of integral characters to the corresponding
real multiples. This identity lets rational-normal constructions clear denominators.
-/

public section

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Real extension carries integer multiples of characters to real scalar multiples. -/
theorem realCharacter_int_smul (h : IsIntegralLattice i) (a : ℤ)
    (m : Module.Dual ℤ N) :
    h.realCharacter (a • m).toAddMonoidHom =
      (a : ℝ) • h.realCharacter m.toAddMonoidHom := by
  symm
  apply h.eq_realCharacter
  intro n
  simp

end TauCeti.Toric.IsIntegralLattice
