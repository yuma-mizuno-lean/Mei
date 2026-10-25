/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
public import Mei.RingTheory.Ideal.Operations

/-!
# Associativity of algebraic BCH

The universal BCH operation is associative in every nilpotent rational Lie algebra,
without freeness or finite-dimensionality assumptions. The proof tests the identity
in a three-generator free nilpotent quotient, where the canonical enveloping map is
injective, and then evaluates its generators in the desired algebra.

The exponential identity uses `Mei.FreeLieAlgebra.exp_quotientEnvelopingMap_bchElement`,
Mathlib's enveloping universal property, and the finite exponential/logarithm inverse
laws. More generally, a Lie representation into a nilpotent associative ideal sends
BCH to multiplication of finite exponentials.
-/

public section

namespace Mei

open LieModule
open Mei.FreeLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type*} [LieRing L] [LieAlgebra ℚ L] [Ring A] [Algebra ℚ A]

/-- A representation into an associative ideal of nilpotency bound `c + 1` sends
the class-`c` BCH operation to the product of finite exponentials. -/
theorem exp_map_bchOfClass (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : I ^ (c + 1) = ⊥)
    (hf : ∀ x, f x ∈ I) (x y : L) :
    IsNilpotent.exp (f (bchOfClass c hc x y)) =
      IsNilpotent.exp (f x) * IsNilpotent.exp (f y) := by
  let F := _root_.FreeLieAlgebra ℚ (Fin 2)
  let J := (TauCeti.HopfIdeal.augmentation ℚ (UniversalEnvelopingAlgebra ℚ F)).toIdeal
  let l := liftLowerCentralQuotient ℚ c hc ![x, y]
  let u := UniversalEnvelopingAlgebra.lift ℚ
    (f.comp (_root_.FreeLieAlgebra.lift ℚ ![x, y]))
  have hu (a) (ha : a ∈ J ^ (c + 1)) : u a = 0 := by
    have h := u.map_mem_augmentation_pow I (by
      intro z
      simpa only [u, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply] using
        hf (_root_.FreeLieAlgebra.lift ℚ ![x, y] z)) (c + 1) ha
    simpa only [hI, Ideal.mem_bot] using h
  let q := Ideal.Quotient.liftₐ (J ^ (c + 1)) u hu
  have hq (a : UniversalEnvelopingAlgebra ℚ F) :
      q (Ideal.Quotient.mk (J ^ (c + 1)) a) = u a := by
    exact AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (J ^ (c + 1)) u hu) a
  have he : q.toLieHom.comp (quotientEnvelopingMap ℚ (Fin 2) c) = f.comp l := by
    apply LieIdeal.lieHom_qext (lowerCentralSeries ℚ F F c)
    intro z
    simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, LieIdeal.mkQ_apply]
    rw [quotientEnvelopingMap_mk ℚ (Fin 2) c z, hq]
    simp only [l, u, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply]
    rw [liftLowerCentralQuotient_mk]
  have h := congrArg q (exp_quotientEnvelopingMap_bchElement c)
  have hnil (z : F) : IsNilpotent (Ideal.Quotient.mk (J ^ (c + 1))
      (UniversalEnvelopingAlgebra.ι ℚ z)) := by
    simpa only [quotientEnvelopingMap_mk] using
      isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c (LieSubmodule.Quotient.mk z)
  rw [IsNilpotent.map_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c _),
    map_mul, IsNilpotent.map_exp (hnil _), IsNilpotent.map_exp (hnil _)] at h
  have he' := LieHom.congr_fun he (bchElement c)
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply] at he'
  rw [he'] at h
  have hl : bchOfClass c hc x y = l (bchElement c) := by
    simpa only [l, liftLowerCentralQuotient_mk, _root_.FreeLieAlgebra.lift_of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using bchOfClass_eq_of_hom c hc l
  rw [hl]
  simpa only [hq, u,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    _root_.FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

namespace FreeLieAlgebra

variable (S : Type*) (c : ℕ)

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "C" => lowerCentralSeries ℚ F F c
local notation "U" => UniversalEnvelopingAlgebra ℚ F
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation ℚ U)

/-- BCH in a free nilpotent quotient exponentiates to multiplication in its
finite augmentation quotient. -/
theorem exp_quotientEnvelopingMap_bchOfClass
    (hc : lowerCentralSeries ℚ (F ⧸ C) (F ⧸ C) c = ⊥) (x y : F ⧸ C) :
    IsNilpotent.exp (quotientEnvelopingMap ℚ S c (bchOfClass c hc x y)) =
      IsNilpotent.exp (quotientEnvelopingMap ℚ S c x) *
        IsNilpotent.exp (quotientEnvelopingMap ℚ S c y) := by
  let I := Ideal.map (Ideal.Quotient.mk (J ^ (c + 1))) J
  have hI : I ^ (c + 1) = ⊥ := by
    rw [← Ideal.map_pow_of_surjective J _ (Ideal.Quotient.mk_surjective) (c + 1)]
    exact Ideal.map_quotient_self (J ^ (c + 1))
  apply exp_map_bchOfClass c hc (quotientEnvelopingMap ℚ S c) I hI
  intro z
  obtain ⟨z, rfl⟩ := LieIdeal.surjective_mkQ C z
  rw [LieIdeal.mkQ_apply, quotientEnvelopingMap_mk]
  exact Ideal.mem_map_of_mem _ (TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation ℚ F z)

end FreeLieAlgebra

/-- Finite BCH evaluation is associative at every valid nilpotency bound. -/
theorem bchOfClass_assoc (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥) (x y z : L) :
    bchOfClass c hc (bchOfClass c hc x y) z =
      bchOfClass c hc x (bchOfClass c hc y z) := by
  let F := _root_.FreeLieAlgebra ℚ (Fin 3)
  let C : LieIdeal ℚ F := lowerCentralSeries ℚ F F c
  let Q := F ⧸ C
  have hQ : lowerCentralSeries ℚ Q Q c = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq c C.surjective_mkQ,
      LieIdeal.map_eq_bot_iff, LieIdeal.mkQ_ker]
  have hfree (a b d : Q) :
      bchOfClass c hQ (bchOfClass c hQ a b) d =
        bchOfClass c hQ a (bchOfClass c hQ b d) := by
    let i := quotientEnvelopingMap ℚ (Fin 3) c
    apply quotientEnvelopingMap_injective ℚ (Fin 3) c
    calc
      i (bchOfClass c hQ (bchOfClass c hQ a b) d) =
          IsNilpotent.log (IsNilpotent.exp
            (i (bchOfClass c hQ (bchOfClass c hQ a b) d))) :=
        (IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 3) c _)).symm
      _ = IsNilpotent.log (IsNilpotent.exp
            (i (bchOfClass c hQ a (bchOfClass c hQ b d)))) := by
        apply congrArg IsNilpotent.log
        simp only [i, exp_quotientEnvelopingMap_bchOfClass (Fin 3) c hQ]
        exact mul_assoc _ _ _
      _ = i (bchOfClass c hQ a (bchOfClass c hQ b d)) :=
        IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 3) c _)
  let f := liftLowerCentralQuotient ℚ c hc ![x, y, z]
  have h := congrArg f (hfree
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0))
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1))
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 2)))
  simp only [f.map_bchOfClass c c hQ hc] at h
  simp only [f] at h
  rw [liftLowerCentralQuotient_mk, liftLowerCentralQuotient_mk,
    liftLowerCentralQuotient_mk] at h
  simpa using h

/-- BCH is associative in every nilpotent rational Lie algebra. -/
theorem bch_assoc [LieRing.IsNilpotent L] (x y z : L) :
    bch (bch x y) z = bch x (bch y z) := by
  obtain ⟨c, hc⟩ := IsNilpotent.nilpotent ℚ L L
  simp only [bch_eq_bchOfClass c hc]
  exact bchOfClass_assoc c hc x y z

end Mei
