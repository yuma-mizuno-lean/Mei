/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Group
public import Mei.Algebra.Lie.InnerAutomorphism
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Conjugation in algebraic BCH groups

Conjugation by `exp x` in a nilpotent rational Lie algebra's BCH group acts on
logarithms by `exp (ad x)`. In particular, a central Lie commutator gives the
three-factor exponential interchange relation.

The identity is tested in a free nilpotent quotient using
`Mei.FreeLieAlgebra.quotientEnvelopingMap_injective` and then evaluated in the
desired Lie algebra. Thus the underlying module need not be free. The associative
calculation uses `TauCeti.expAd_apply_eq_exp_mul_exp_neg`, Mathlib's
`IsNilpotent.exp_smul`, and the finite BCH exponential identity.
The associative conjugation calculation adapts the private
`exp_mul_exp_mul_exp_neg` argument in `TauCeti.Algebra.Lie.InnerAutomorphism`.
-/

public section

namespace Mei

open LieModule
open Mei.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- Finite BCH conjugation is the exponential adjoint action, at every valid
nilpotency bound. -/
theorem bchOfClass_conj (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (x y : L) (hx : IsNilpotent (LieAlgebra.ad ℚ L x)) :
    bchOfClass c hc (bchOfClass c hc x y) (-x) = TauCeti.expAd x hx y := by
  let F := _root_.FreeLieAlgebra ℚ (Fin 2)
  let C : LieIdeal ℚ F := lowerCentralSeries ℚ F F c
  let Q := F ⧸ C
  have hQ : lowerCentralSeries ℚ Q Q c = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq c C.surjective_mkQ,
      LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  let : LieRing.IsNilpotent Q := (LieModule.isNilpotent_iff ℚ Q Q).mpr ⟨c, hQ⟩
  have hnil (a : Q) : IsNilpotent (LieAlgebra.ad ℚ Q a) :=
    isNilpotent_toEnd_of_isNilpotent ℚ Q Q a
  have hfree (a b : Q) :
      bchOfClass c hQ (bchOfClass c hQ a b) (-a) =
        TauCeti.expAd a (hnil a) b := by
    let i := quotientEnvelopingMap ℚ (Fin 2) c
    have ha := isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c a
    have hb := isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c b
    have hconj : IsNilpotent.exp (i a) * IsNilpotent.exp (i b) *
        IsNilpotent.exp (-i a) =
          IsNilpotent.exp (i (TauCeti.expAd a (hnil a) b)) := by
      rw [i.map_expAd a b _ (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) ha),
        TauCeti.expAd_apply_eq_exp_mul_exp_neg ha]
      simpa only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct,
        TauCeti.coe_nilpotentExpUnit, TauCeti.coe_inv_nilpotentExpUnit] using
        (IsNilpotent.exp_smul (ConjAct.toConjAct (TauCeti.nilpotentExpUnit ha)) hb).symm
    apply quotientEnvelopingMap_injective ℚ (Fin 2) c
    apply (IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c _)).symm.trans
    rw [exp_quotientEnvelopingMap_bchOfClass, exp_quotientEnvelopingMap_bchOfClass,
      map_neg, hconj]
    exact IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c _)
  let a : Q := LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)
  let b : Q := LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1)
  let f := liftLowerCentralQuotient ℚ c hc ![x, y]
  have hfa : f a = x := by
    dsimp only [f, a]
    rw [liftLowerCentralQuotient_mk]
    simp
  have hfb : f b = y := by
    dsimp only [f, b]
    rw [liftLowerCentralQuotient_mk]
    simp
  have h := congrArg f (hfree a b)
  rw [f.map_bchOfClass c c hQ hc, f.map_bchOfClass c c hQ hc, map_neg,
    f.map_expAd a b _ (by rw [hfa]; exact hx)] at h
  simpa only [hfa, hfb] using h

variable [LieRing.IsNilpotent L] {R : Type*} [CommRing R] [LieAlgebra R L]

/-- BCH conjugation is the exponential adjoint action. -/
theorem bch_conj (x y : L) (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    bch (bch x y) (-x) = TauCeti.expAd x hx y := by
  obtain ⟨c, hc⟩ := IsNilpotent.nilpotent ℚ L L
  have hx' : IsNilpotent (LieAlgebra.ad ℚ L x) :=
    isNilpotent_toEnd_of_isNilpotent ℚ L L x
  simp only [bch_eq_bchOfClass c hc]
  exact (bchOfClass_conj c hc x y hx').trans (expAd_apply_eq_expAd ℚ R x y hx' hx)

namespace BCHGroup

/-- Conjugation in the BCH group exponentiates the adjoint action. -/
@[simp]
theorem exp_expAd (x y : L) (hx : IsNilpotent (LieAlgebra.ad R L x)) :
    exp (TauCeti.expAd x hx y) = exp x * exp y * (exp x)⁻¹ := by
  rw [← bch_conj x y hx, exp_bch, exp_bch, exp_neg]

/-- When the commutator is central relative to both inputs, exponentials can be
interchanged by inserting the exponential of that commutator. -/
theorem exp_mul_exp_eq_exp_mul_exp_mul {x y z : L}
    (hxy : ⁅x, y⁆ = z) (hxz : ⁅x, z⁆ = 0) (hyz : ⁅y, z⁆ = 0) :
    exp x * exp y = exp y * exp z * exp x := by
  have hx : IsNilpotent (LieAlgebra.ad ℚ L x) :=
    isNilpotent_toEnd_of_isNilpotent ℚ L L x
  have h := exp_expAd x y hx
  rw [TauCeti.expAd_apply_of_lie_lie_eq_zero hx (by rw [hxy]; exact hxz), hxy,
    exp_add_of_lie_eq_zero y z hyz] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

end BCHGroup
end Mei
