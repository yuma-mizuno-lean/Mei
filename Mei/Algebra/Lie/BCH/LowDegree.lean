/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Basic

/-!
# BCH formulas in small nilpotency classes

The universal degree-three formula evaluates in every rational Lie algebra of
nilpotency class at most three. For class at most two it reduces to
`x + y + ⁅x, y⁆ / 2`. These are formulas for the actual universal BCH operation,
without a choice of faithful representation.

The calculation uses `Mei.FreeLieAlgebra.bchElement_three` and the universal
evaluation map `Mei.FreeLieAlgebra.liftLowerCentralQuotient`. The associative
polynomial calculation underlying the universal formula is supplied by
`Ideal.log_exp_mul_exp_of_pow_four_eq_bot`.
-/

public section

namespace Mei

open LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- In class at most three, BCH is the universal polynomial through degree three. -/
@[simp]
theorem bchOfClass_three (hc : lowerCentralSeries ℚ L L 3 = ⊥) (x y : L) :
    bchOfClass 3 hc x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
      (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  have h := bchOfClass_eq_of_hom 3 hc
    (FreeLieAlgebra.liftLowerCentralQuotient ℚ 3 hc ![x, y])
  simpa [FreeLieAlgebra.liftLowerCentralQuotient_mk] using h

/-- In class at most two, only the half-commutator correction remains. -/
@[simp]
theorem bchOfClass_two (hc : lowerCentralSeries ℚ L L 2 = ⊥) (x y : L) :
    bchOfClass 2 hc x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  have hc₃ : lowerCentralSeries ℚ L L 3 = ⊥ :=
    eq_bot_iff.mpr ((antitone_lowerCentralSeries ℚ L L (by decide : 2 ≤ 3)).trans hc.le)
  have hvanish (a b c : L) : ⁅a, ⁅b, c⁆⁆ = 0 := by
    have h : ⁅a, ⁅b, c⁆⁆ ∈ lowerCentralSeries ℚ L L 2 := by
      rw [lowerCentralSeries_succ]
      apply LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a)
      rw [lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b) (by simp)
    simpa only [hc, LieSubmodule.mem_bot] using h
  rw [bchOfClass_eq 2 3 hc hc₃, bchOfClass_three]
  simp only [hvanish, add_zero, smul_zero]

variable [LieRing.IsNilpotent L]

/-- Any class-three bound computes the bound-independent BCH operation. -/
theorem bch_eq_of_class_three (hc : lowerCentralSeries ℚ L L 3 = ⊥) (x y : L) :
    bch x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
      (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  rw [bch_eq_bchOfClass 3 hc, bchOfClass_three]

/-- Any class-two bound computes BCH by the half-commutator formula. -/
theorem bch_eq_of_class_two (hc : lowerCentralSeries ℚ L L 2 = ⊥) (x y : L) :
    bch x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  rw [bch_eq_bchOfClass 2 hc, bchOfClass_two]

end Mei
