/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Enveloping
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Reconstruction

/-!
# Primitive elements in a free Lie enveloping algebra

Specializing the integral-degree reconstruction theorem to word length, the Euler
derivation and its Dynkin operator detect the canonical Lie image without assuming
that homogeneous components of a primitive element are themselves primitive. The same
inverse-Euler calculation reconstructs Lie representatives modulo augmentation powers.
-/

public section

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] (S : Type*)
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "ℒ" => homogeneousSubmodule R S
local notation "E" => LieDerivation.ofGrading ℒ (Nat.castAddMonoidHom R)
local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R F E
local notation "T" => Mei.HopfAlgebra.dynkinOperator Y
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

variable [Algebra ℚ R]

local notation "δ" => Nat.castAddMonoidHom ℤ
local notation "𝓕" => Mei.UniversalEnvelopingAlgebra.degreeFiltration ℒ δ
  (fun n hn => False.elim (not_lt_of_ge (Int.natCast_nonneg n) hn))

/-- An augmentation element whose Dynkin and Euler values agree through order `N` is
congruent to an actual free Lie element through the same order. -/
theorem exists_sub_ι_mem_augmentation_pow_of_dynkin_sub_mem {a : U} {N : ℕ}
    (ha : a ∈ J) (h : T a - (Y : Module.End R U) a ∈ J ^ N) :
    ∃ x : F, a - _root_.UniversalEnvelopingAlgebra.ι R x ∈ J ^ N := by
  have hw : (Int.castAddHom R).comp δ = Nat.castAddMonoidHom R :=
    AddMonoidHom.ext (fun n => by simp)
  have ha' : a ∈ (𝓕).ideal 1 := by
    simpa only [degreeFiltration_eq_augmentation_pow, Submodule.pow_one] using ha
  rw [← degreeFiltration_eq_augmentation_pow R S N, ← hw] at h
  simpa only [degreeFiltration_eq_augmentation_pow] using
    Mei.UniversalEnvelopingAlgebra.exists_sub_ι_mem_degreeFiltration_of_dynkin_sub_mem
      ℒ δ _ ha' h

/-- The primitive elements in the enveloping algebra of a free Lie algebra over a rational
algebra are exactly its canonical Lie image. -/
theorem isPrimitiveElem_iff_mem_range_ι (a : U) :
    Bialgebra.IsPrimitiveElem R a ↔
      a ∈ (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap.range := by
  constructor
  · intro hp
    have ha : a ∈ (𝓕).ideal 1 := by
      rw [degreeFiltration_eq_augmentation_pow, Submodule.pow_one]
      exact (TauCeti.HopfIdeal.mem_augmentation R U).mpr hp.counit_eq_zero
    have hw : (Int.castAddHom R).comp δ = Nat.castAddMonoidHom R :=
      AddMonoidHom.ext (fun n => by simp)
    have h := Mei.HopfAlgebra.dynkinOperator_of_isPrimitiveElem Y hp
    rw [← hw] at h
    exact Mei.UniversalEnvelopingAlgebra.exists_ι_eq_of_dynkin_eq ℒ δ _ ha h
  · rintro ⟨x, rfl⟩
    have hp : Bialgebra.IsPrimitiveElem R (_root_.UniversalEnvelopingAlgebra.ι R x) :=
      ⟨TauCeti.UniversalEnvelopingAlgebra.counit_ι R F x, by
        rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι]
        exact add_comm _ _⟩
    simpa only [LieHom.coe_toLinearMap] using hp

end Mei.FreeLieAlgebra
