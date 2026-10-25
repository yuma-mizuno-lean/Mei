/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Primitive.Truncation
public import Mei.Algebra.Lie.UniversalEnveloping.PrimitiveBCH

/-!
# Universal finite BCH elements

For every nilpotency class, the logarithm of the product of two generator exponentials
belongs to the canonical image of the free nilpotent Lie algebra. The primitive identity
is interpreted in the total tensor quotient, and the image criterion reconstructs an
actual Lie element. Injectivity of the quotient enveloping map gives uniqueness.

The construction uses the equality of word-degree ideals and augmentation powers,
transporting exponential and logarithm through the resulting quotient equivalence.
It defines the universal finite BCH element; group operations and their laws are separate.
-/

public section

open scoped TensorProduct

namespace Mei.FreeLieAlgebra

variable (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ F
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation ℚ U)
local notation "ℒ" => homogeneousSubmodule ℚ S
local notation "δ" => Nat.castAddMonoidHom ℤ
local notation "𝓕" => Mei.UniversalEnvelopingAlgebra.degreeFiltration ℒ δ
  (fun n hn => False.elim (not_lt_of_ge (Int.natCast_nonneg n) hn))
local notation "T" => Ideal.tensorFiltration ℚ (fun n => J ^ n) (fun n => J ^ n)

/-- The finite BCH logarithm has an augmentation representative primitive modulo total degree. -/
theorem exists_primitive_representative_log_exp_product (c : ℕ) (x y : F) :
    ∃ a : U, a ∈ J ∧
      Coalgebra.comul a - 1 ⊗ₜ[ℚ] a - a ⊗ₜ[ℚ] 1 ∈ T (c + 1) ∧
      Ideal.Quotient.mk (J ^ (c + 1)) a =
        IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ y))) ∧
      IsNilpotent (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) - 1) := by
  have hpos : ∀ n, δ n ≤ 0 → ℒ n = ⊥ := by
    intro n hn
    have hn0 : n = 0 := by change (n : ℤ) ≤ 0 at hn; omega
    subst n
    exact homogeneousSubmodule_zero ℚ S
  -- Work first in the degree quotient, where the coproduct identity is available.
  let q := Ideal.Quotient.mk ((𝓕).ideal (c + 1))
  let g := IsNilpotent.exp (q (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
    IsNilpotent.exp (q (_root_.UniversalEnvelopingAlgebra.ι ℚ y))
  let π : U ⧸ (𝓕).ideal (c + 1) →+* U ⧸ (𝓕).ideal 1 :=
    Ideal.Quotient.factor ((𝓕).antitone (Nat.le_add_left 1 c))
  have hnil (b : U ⧸ (𝓕).ideal (c + 1)) (hb : π b = 0) : IsNilpotent b :=
    (𝓕).isNilpotent_of_factor_eq_zero c b hb
  have hp (z : F) : π (q (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Mei.UniversalEnvelopingAlgebra.ι_mem_degreeFiltration_one ℒ δ hpos z
  have hg1 : π g = 1 := by
    rw [map_mul, IsNilpotent.map_exp (hnil _ (hp x)),
      IsNilpotent.map_exp (hnil _ (hp y)), hp x, hp y, IsNilpotent.exp_zero, one_mul]
  have hgu : IsNilpotent (g - 1) := hnil _ (by rw [map_sub, map_one, hg1, sub_self])
  -- Lift the finite logarithm and interpret its primitive identity on representatives.
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (IsNilpotent.log g)
  have hprim := Mei.UniversalEnvelopingAlgebra.quotient_log_exp_product_primitive
    ℒ δ hpos c x y
  change Mei.UniversalEnvelopingAlgebra.quotientCoproduct ℒ δ _ (c + 1)
      (IsNilpotent.log g) = _ at hprim
  rw [← ha] at hprim
  simp only [Mei.UniversalEnvelopingAlgebra.quotientCoproduct_mk,
    Mei.AlgFiltration.quotientIncludeLeft_mk,
    Mei.AlgFiltration.quotientIncludeRight_mk] at hprim
  have hred : Coalgebra.comul a - 1 ⊗ₜ[ℚ] a - a ⊗ₜ[ℚ] 1 ∈ T (c + 1) := by
    have ht : (fun n => (𝓕).ideal n) = (fun n => J ^ n) :=
      funext (degreeFiltration_eq_augmentation_pow ℚ S)
    rw [← ht]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_sub]
    rw [hprim]
    abel
  refine ⟨a, ?_, hred, ?_⟩
  · have hz : π (IsNilpotent.log g) = 0 := by
      rw [IsNilpotent.map_log hgu, hg1, IsNilpotent.log_one]
    have ha1 : a ∈ (𝓕).ideal 1 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [← ha, π, Ideal.Quotient.factor_mk] using hz
    simpa only [degreeFiltration_eq_augmentation_pow ℚ S, Submodule.pow_one] using ha1
  -- Transport the logarithm to the actual augmentation quotient.
  · let e := Ideal.quotientEquivAlgOfEq ℚ (degreeFiltration_eq_augmentation_pow ℚ S (c + 1))
    have hh := congrArg e ha
    rw [IsNilpotent.map_log hgu, map_mul, IsNilpotent.map_exp (hnil _ (hp x)),
      IsNilpotent.map_exp (hnil _ (hp y))] at hh
    refine ⟨?_, ?_⟩
    · simpa only [e, q, Ideal.quotientEquivAlgOfEq_mk] using hh
    · have hm := hgu.map e
      rw [map_sub, map_one, map_mul, IsNilpotent.map_exp (hnil _ (hp x)),
        IsNilpotent.map_exp (hnil _ (hp y))] at hm
      simpa only [e, q, Ideal.quotientEquivAlgOfEq_mk] using hm

/-- Every element of the canonical Lie image in the finite augmentation quotient is nilpotent. -/
theorem isNilpotent_quotientEnvelopingMap (c : ℕ)
    (z : F ⧸ LieModule.lowerCentralSeries ℚ F F c) :
    IsNilpotent (quotientEnvelopingMap ℚ S c z) := by
  induction z using Quotient.inductionOn' with | _ z =>
  change IsNilpotent (quotientEnvelopingMap ℚ S c (LieSubmodule.Quotient.mk z))
  rw [quotientEnvelopingMap_mk]
  refine ⟨c + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.pow_mem_pow
  simpa only [pow_one] using
    TauCeti.UniversalEnvelopingAlgebra.pow_ι_mem_augmentation_toIdeal ℚ F z (by decide : 1 ≠ 0)

/-- Exponential products have unique preimages in the free nilpotent Lie quotient. -/
theorem existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp (c : ℕ) (x y : F) :
    ∃! z : F ⧸ LieModule.lowerCentralSeries ℚ F F c,
      IsNilpotent.exp (quotientEnvelopingMap ℚ S c z) =
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) := by
  obtain ⟨a, ha, hred, himage, hnil⟩ := exists_primitive_representative_log_exp_product S c x y
  obtain ⟨z, hz⟩ := quotient_mem_range_quotientEnvelopingMap_of_reducedComul_mem ℚ S c ha hred
  have hzlog := hz.trans himage
  change quotientEnvelopingMap ℚ S c z = _ at hzlog
  refine ⟨z, ?_, ?_⟩
  · dsimp only
    rw [hzlog, IsNilpotent.exp_log hnil]
  · intro w hw
    apply quotientEnvelopingMap_injective ℚ S c
    rw [hzlog, ← hw, IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap S c w)]


/-- The finite logarithm of an exponential product belongs to the canonical Lie image. -/
theorem log_exp_product_mem_range_quotientEnvelopingMap (c : ℕ) (x y : F) :
    IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ y))) ∈ (quotientEnvelopingMap ℚ S c).range := by
  obtain ⟨z, hz, _⟩ := existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp S c x y
  refine ⟨z, ?_⟩
  change quotientEnvelopingMap ℚ S c z = _
  rw [← hz, IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap S c z)]

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation ℚ U₂)
local notation "X" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)

/-- The universal finite BCH element in the two-generator free nilpotent Lie algebra. -/
noncomputable def bchElement (c : ℕ) :
    F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c :=
  Classical.choose (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp (Fin 2) c X Y)

/-- The universal BCH element exponentiates to the ordered product of generator exponentials. -/
theorem exp_quotientEnvelopingMap_bchElement (c : ℕ) :
    IsNilpotent.exp (quotientEnvelopingMap ℚ (Fin 2) c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) :=
  (Classical.choose_spec
    (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp (Fin 2) c X Y)).1

/-- The canonical image of the universal BCH element is the finite logarithm of the product. -/
theorem quotientEnvelopingMap_bchElement (c : ℕ) :
    quotientEnvelopingMap ℚ (Fin 2) c (bchElement c) =
      IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y))) := by
  rw [← exp_quotientEnvelopingMap_bchElement,
    IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap (Fin 2) c (bchElement c))]

/-- The exponential identity uniquely characterizes the universal finite BCH element. -/
theorem bchElement_unique (c : ℕ)
    (z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c)
    (hz : IsNilpotent.exp (quotientEnvelopingMap ℚ (Fin 2) c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y))) : z = bchElement c :=
  (Classical.choose_spec
    (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp (Fin 2) c X Y)).2 z hz

end Mei.FreeLieAlgebra
