/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.LowDegree
public import Mei.Algebra.Lie.BCH.Group
public import TauCeti.Algebra.Lie.Heisenberg

/-!
# BCH multiplication in the Heisenberg Lie algebra

The BCH operation on the three-dimensional Heisenberg Lie algebra is addition
with the half-commutator correction. In particular, the two orders of the standard
generator exponentials have opposite central corrections, and the BCH
group is noncommutative over every nontrivial commutative rational algebra.

We use Tau Ceti's concrete Heisenberg algebra, its bracket table and its class-two
nilpotency theorem, together with `Mei.bch_eq_of_class_two`.
-/

public section

namespace Mei

open TauCeti LieModule BCHGroup

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- BCH on the Heisenberg Lie algebra has exactly the half-commutator correction. -/
@[simp]
theorem bch_heisenberg (x y : heisenberg R) :
    bch x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  have hc : lowerCentralSeries ℚ (heisenberg R) (heisenberg R) 2 = ⊥ := by
    apply SetLike.coe_injective
    rw [coe_lowerCentralSeries_eq_int ℚ,
      ← coe_lowerCentralSeries_eq_int R, lowerCentralSeries_heisenberg_two]
    rfl
  exact bch_eq_of_class_two hc x y

/-- The standard ordered generator product has positive central correction. -/
theorem log_exp_heisenbergX_mul_exp_heisenbergY :
    log (exp (heisenbergX R) * exp (heisenbergY R)) =
      heisenbergX R + heisenbergY R + (1 / 2 : ℚ) • heisenbergZ R := by
  simp

/-- Reversing the two standard generators changes the sign of the central correction. -/
theorem log_exp_heisenbergY_mul_exp_heisenbergX :
    log (exp (heisenbergY R) * exp (heisenbergX R)) =
      heisenbergX R + heisenbergY R - (1 / 2 : ℚ) • heisenbergZ R := by
  simp [add_comm, sub_eq_add_neg]

/-- The standard generator exponentials do not commute over a nontrivial coefficient ring. -/
theorem exp_heisenbergX_mul_exp_heisenbergY_ne [Nontrivial R] :
    exp (heisenbergX R) * exp (heisenbergY R) ≠
      exp (heisenbergY R) * exp (heisenbergX R) := by
  intro h
  have he := congrArg log h
  rw [log_exp_heisenbergX_mul_exp_heisenbergY,
    log_exp_heisenbergY_mul_exp_heisenbergX] at he
  have hz : heisenbergZ R = 0 := by
    have hhalf : (1 / 2 : ℚ) • heisenbergZ R = -((1 / 2 : ℚ) • heisenbergZ R) :=
      add_left_cancel (he.trans (sub_eq_add_neg _ _))
    have hzero : (1 : ℚ) • heisenbergZ R = 0 := by
      calc
        (1 : ℚ) • heisenbergZ R =
            (1 / 2 : ℚ) • heisenbergZ R + (1 / 2 : ℚ) • heisenbergZ R := by
              rw [← add_smul]; norm_num
        _ = 0 := eq_neg_iff_add_eq_zero.mp hhalf
    simpa using hzero
  exact heisenbergZ_ne_zero hz

end Mei
