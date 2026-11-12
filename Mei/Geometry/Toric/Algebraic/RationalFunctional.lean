/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.RationalFunctional

/-!
# Kernels and scaling of rational functionals

A real scalar with a rational witness preserves rationality. The kernel of a
rational functional is the kernel of the real extension of an integral character.
-/

public section

open TauCeti.Toric (IsRationalFunctional)

namespace TauCeti.Toric.IsRationalFunctional

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i} {f : Module.Dual ℝ V}

/-- The scalar may equivalently be supplied as a real number with a rational witness. -/
theorem smul (hf : IsRationalFunctional h f) {a : ℝ}
    (ha : ∃ q : ℚ, a = (q : ℝ)) : IsRationalFunctional h (a • f) := by
  obtain ⟨q, rfl⟩ := ha
  exact hf.rat_smul q

/-- A rational functional has the same kernel as an integral character's real
extension. The zero functional is allowed, using the zero character. -/
theorem exists_ker_eq_realCharacter (hf : IsRationalFunctional h f) :
    ∃ m : Module.Dual ℤ N, f.ker = (h.realCharacter m.toAddMonoidHom).ker := by
  obtain ⟨q, m, rfl⟩ := iff_exists_character.mp hf
  by_cases hq : q = 0
  · refine ⟨0, ?_⟩
    rw [hq, Rat.cast_zero, zero_smul]
    have hz : (0 : Module.Dual ℤ N).toAddMonoidHom = 0 := (rfl)
    rw [hz, map_zero]
  · exact ⟨m, LinearMap.ker_smul _ (q : ℝ) (by exact_mod_cast hq)⟩

end TauCeti.Toric.IsRationalFunctional
