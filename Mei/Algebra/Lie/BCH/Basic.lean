/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.BCH

/-!
# Evaluation of the universal BCH element

The finite universal BCH element evaluates in every nilpotent rational Lie algebra.
The resulting operation is independent of the nilpotency bound and commutes with
Lie homomorphisms. This gives a bound-independent candidate for multiplication in
exponential coordinates, without requiring a faithful representation or a free
underlying module.

The construction uses `Mei.FreeLieAlgebra.liftLowerCentralQuotient`; independence
of bounds follows from `Mei.FreeLieAlgebra.factor_bchElement`.
-/

public section

namespace Mei

open LieModule
open Mei.FreeLieAlgebra (liftLowerCentralQuotient liftLowerCentralQuotient_mk)

variable {L L' : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing L'] [LieAlgebra ℚ L']

local notation "Free₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "C" => lowerCentralSeries ℚ Free₂ Free₂

/-- Evaluate the universal finite BCH element using a specified nilpotency bound.
The bound uses Mathlib's zero-based lower central series. -/
noncomputable def bchOfClass (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (x y : L) : L :=
  liftLowerCentralQuotient ℚ c hc ![x, y] (FreeLieAlgebra.bchElement c)

/-- Any Lie homomorphism out of the free nilpotent quotient computes BCH from its
values on the two free generators. -/
theorem bchOfClass_eq_of_hom (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (f : Free₂ ⧸ C c →ₗ⁅ℚ⁆ L) :
    bchOfClass c hc
        (f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)))
        (f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1))) =
      f (FreeLieAlgebra.bchElement c) := by
  have he : liftLowerCentralQuotient ℚ c hc
      ![f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)),
        f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1))] = f := by
    apply LieIdeal.lieHom_qext (C c)
    intro z
    suffices h : (liftLowerCentralQuotient ℚ c hc
        ![f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)),
          f (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1))]).comp
          (LieIdeal.mkQ (C c)) = f.comp (LieIdeal.mkQ (C c)) from by
      simpa only [LieHom.comp_apply] using LieHom.congr_fun h z
    apply _root_.FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [LieHom.comp_apply, LieIdeal.mkQ_apply, liftLowerCentralQuotient_mk]
  rw [bchOfClass, he]

/-- A larger nilpotency bound gives the same BCH operation. -/
private theorem bchOfClass_eq_of_le {c d : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥)
    (hd : lowerCentralSeries ℚ L L d = ⊥) (h : c ≤ d) (x y : L) :
    bchOfClass d hd x y = bchOfClass c hc x y := by
  have he : (liftLowerCentralQuotient ℚ c hc ![x, y]).comp
      (LieIdeal.factor (C d) (C c) (antitone_lowerCentralSeries ℚ Free₂ Free₂ h)) =
        liftLowerCentralQuotient ℚ d hd ![x, y] := by
    apply LieIdeal.lieHom_qext (C d)
    intro z
    simp [LieHom.comp_apply, LieIdeal.mkQ_apply, liftLowerCentralQuotient_mk]
  rw [bchOfClass, ← he, LieHom.comp_apply, FreeLieAlgebra.factor_bchElement h]
  rfl

/-- BCH evaluation is independent of any two valid nilpotency bounds. -/
theorem bchOfClass_eq (c d : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (hd : lowerCentralSeries ℚ L L d = ⊥) (x y : L) :
    bchOfClass c hc x y = bchOfClass d hd x y := by
  rcases le_total c d with h | h
  · exact (bchOfClass_eq_of_le hc hd h x y).symm
  · exact bchOfClass_eq_of_le hd hc h x y

/-- Lie homomorphisms preserve finite BCH evaluation, even when the source and target
use different nilpotency bounds. -/
theorem _root_.LieHom.map_bchOfClass (f : L →ₗ⁅ℚ⁆ L') (c d : ℕ)
    (hc : lowerCentralSeries ℚ L L c = ⊥) (hd : lowerCentralSeries ℚ L' L' d = ⊥)
    (x y : L) :
    f (bchOfClass c hc x y) = bchOfClass d hd (f x) (f y) := by
  let n := max c d
  have hc' : lowerCentralSeries ℚ L L n = ⊥ :=
    eq_bot_iff.mpr ((antitone_lowerCentralSeries ℚ L L (le_max_left c d)).trans hc.le)
  have hd' : lowerCentralSeries ℚ L' L' n = ⊥ :=
    eq_bot_iff.mpr ((antitone_lowerCentralSeries ℚ L' L' (le_max_right c d)).trans hd.le)
  rw [← bchOfClass_eq_of_le hc hc' (le_max_left c d),
    ← bchOfClass_eq_of_le hd hd' (le_max_right c d)]
  have he := bchOfClass_eq_of_hom n hd' (f.comp (liftLowerCentralQuotient ℚ n hc' ![x, y]))
  simp only [LieHom.comp_apply, liftLowerCentralQuotient_mk, _root_.FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at he
  exact he.symm

/-- The bound-one BCH operation is addition. -/
@[simp]
theorem bchOfClass_one (hc : lowerCentralSeries ℚ L L 1 = ⊥) (x y : L) :
    bchOfClass 1 hc x y = x + y := by
  rw [bchOfClass, FreeLieAlgebra.bchElement_one, liftLowerCentralQuotient_mk]
  simp

section Nilpotent

variable [LieRing.IsNilpotent L]

/-- BCH in a nilpotent rational Lie algebra, evaluated at any valid nilpotency bound. -/
noncomputable def bch (x y : L) : L :=
  bchOfClass (Classical.choose (IsNilpotent.nilpotent ℚ L L))
    (Classical.choose_spec (IsNilpotent.nilpotent ℚ L L)) x y

/-- Any explicit nilpotency bound computes the bound-independent BCH operation. -/
theorem bch_eq_bchOfClass (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥) (x y : L) :
    bch x y = bchOfClass c hc x y := by
  exact bchOfClass_eq _ _ _ _ x y

/-- BCH commutes with Lie homomorphisms between nilpotent rational Lie algebras. -/
@[simp]
theorem _root_.LieHom.map_bch [LieRing.IsNilpotent L'] (f : L →ₗ⁅ℚ⁆ L') (x y : L) :
    f (bch x y) = bch (f x) (f y) := by
  exact f.map_bchOfClass _ _ _ _ x y

end Nilpotent

/-- BCH is addition in an abelian rational Lie algebra. -/
@[simp]
theorem bch_eq_add [IsLieAbelian L] (x y : L) : bch x y = x + y := by
  rw [bch_eq_bchOfClass 1 ((trivial_iff_lower_central_eq_bot ℚ L L).mp inferInstance)]
  exact bchOfClass_one _ x y

section Nilpotent

variable [LieRing.IsNilpotent L]

/-- Commuting elements have additive BCH, even in a nonabelian nilpotent Lie algebra. -/
theorem bch_eq_add_of_lie_eq_zero (x y : L) (h : ⁅x, y⁆ = 0) : bch x y = x + y := by
  let K := LieSubalgebra.lieSpan ℚ L {x, y}
  have hK : IsLieAbelian K := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact lie_self _
    · exact h
    · simpa only [lie_skew, neg_zero] using congrArg Neg.neg h
    · exact lie_self _
  let := hK
  let x' : K := ⟨x, LieSubalgebra.subset_lieSpan (by simp)⟩
  let y' : K := ⟨y, LieSubalgebra.subset_lieSpan (by simp)⟩
  have he := K.incl.map_bch x' y'
  rw [bch_eq_add] at he
  exact he.symm

/-- Zero is a left identity for BCH. -/
@[simp]
theorem bch_zero_left (x : L) : bch 0 x = x := by
  simpa using bch_eq_add_of_lie_eq_zero 0 x (zero_lie x)

/-- Zero is a right identity for BCH. -/
@[simp]
theorem bch_zero_right (x : L) : bch x 0 = x := by
  simpa using bch_eq_add_of_lie_eq_zero x 0 (lie_zero x)

/-- Negation gives a right inverse for BCH. -/
@[simp]
theorem bch_neg_right (x : L) : bch x (-x) = 0 := by
  simpa using bch_eq_add_of_lie_eq_zero x (-x) (by simp)

/-- Negation gives a left inverse for BCH. -/
@[simp]
theorem bch_neg_left (x : L) : bch (-x) x = 0 := by
  simpa using bch_eq_add_of_lie_eq_zero (-x) x (by simp)

end Nilpotent

end Mei
