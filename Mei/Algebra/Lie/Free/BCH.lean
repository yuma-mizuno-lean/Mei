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

variable (R : Type*) [CommRing R] [Algebra ℚ R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)
local notation "ℒ" => homogeneousSubmodule R S
local notation "δ" => Nat.castAddMonoidHom ℤ
local notation "𝓕" => Mei.UniversalEnvelopingAlgebra.degreeFiltration ℒ δ
  (fun n hn => False.elim (not_lt_of_ge (Int.natCast_nonneg n) hn))
local notation "T" => Ideal.tensorFiltration R (fun n => J ^ n) (fun n => J ^ n)

/-- The rational scalar action induced from the coefficient algebra. -/
noncomputable local instance ratAlgebraEnveloping : Algebra ℚ U :=
  Algebra.compHom U (algebraMap ℚ R)

/-- The finite BCH logarithm has an augmentation representative primitive modulo total degree. -/
theorem exists_primitive_representative_log_exp_product (c : ℕ) (x y : F) :
    ∃ a : U, a ∈ J ∧
      Coalgebra.comul a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T (c + 1) ∧
      Ideal.Quotient.mk (J ^ (c + 1)) a =
        IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι R x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι R y))) ∧
      IsNilpotent (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι R x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι R y)) - 1) := by
  have hpos : ∀ n, δ n ≤ 0 → ℒ n = ⊥ := by
    intro n hn
    have hn0 : n = 0 := by
      have hn' : (n : ℤ) ≤ 0 := hn
      omega
    subst n
    exact homogeneousSubmodule_zero R S
  -- Work first in the degree quotient, where the coproduct identity is available.
  let q := Ideal.Quotient.mk ((𝓕).ideal (c + 1))
  let g := IsNilpotent.exp (q (_root_.UniversalEnvelopingAlgebra.ι R x)) *
    IsNilpotent.exp (q (_root_.UniversalEnvelopingAlgebra.ι R y))
  let π : U ⧸ (𝓕).ideal (c + 1) →+* U ⧸ (𝓕).ideal 1 :=
    Ideal.Quotient.factor ((𝓕).antitone (Nat.le_add_left 1 c))
  have hnil (b : U ⧸ (𝓕).ideal (c + 1)) (hb : π b = 0) : IsNilpotent b :=
    (𝓕).isNilpotent_of_factor_eq_zero c b hb
  have hp (z : F) : π (q (_root_.UniversalEnvelopingAlgebra.ι R z)) = 0 := by
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
  -- The primitive theorem uses let-bound quotient maps and logarithms. Expose
  -- those lets as our local g; this is reduction, with no equality lemma to rewrite.
  change Mei.UniversalEnvelopingAlgebra.quotientCoproduct ℒ δ _ (c + 1)
      (IsNilpotent.log g) = _ at hprim
  rw [← ha] at hprim
  simp only [Mei.UniversalEnvelopingAlgebra.quotientCoproduct_mk,
    Mei.AlgFiltration.quotientIncludeLeft_mk,
    Mei.AlgFiltration.quotientIncludeRight_mk] at hprim
  have hred : Coalgebra.comul a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T (c + 1) := by
    have ht : (fun n => (𝓕).ideal n) = (fun n => J ^ n) :=
      funext (degreeFiltration_eq_augmentation_pow R S)
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
    simpa only [degreeFiltration_eq_augmentation_pow R S, Submodule.pow_one] using ha1
  -- Transport the logarithm to the actual augmentation quotient.
  · let e := Ideal.quotientEquivAlgOfEq R (degreeFiltration_eq_augmentation_pow R S (c + 1))
    have hh := congrArg e ha
    rw [IsNilpotent.map_log hgu, map_mul, IsNilpotent.map_exp (hnil _ (hp x)),
      IsNilpotent.map_exp (hnil _ (hp y))] at hh
    refine ⟨?_, ?_⟩
    · simpa only [e, q, Ideal.quotientEquivAlgOfEq_mk] using hh
    · have hm := hgu.map e
      rw [map_sub, map_one, map_mul, IsNilpotent.map_exp (hnil _ (hp x)),
        IsNilpotent.map_exp (hnil _ (hp y))] at hm
      simpa only [e, q, Ideal.quotientEquivAlgOfEq_mk] using hm

/-- Exponential products have unique preimages in the free nilpotent Lie quotient. -/
theorem existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp [Module.Free R F] (c : ℕ) (x y : F) :
    ∃! z : F ⧸ LieModule.lowerCentralSeries R F F c,
      IsNilpotent.exp (quotientEnvelopingMap R S c z) =
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι R x)) *
        IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
          (_root_.UniversalEnvelopingAlgebra.ι R y)) := by
  obtain ⟨a, ha, hred, himage, hnil⟩ := exists_primitive_representative_log_exp_product R S c x y
  obtain ⟨z, hz⟩ := quotient_mem_range_quotientEnvelopingMap_of_reducedComul_mem R S c ha hred
  have hzlog := hz.trans himage
  rw [LieHom.coe_toLinearMap] at hzlog
  refine ⟨z, ?_, ?_⟩
  · dsimp only
    rw [hzlog, IsNilpotent.exp_log hnil]
  · intro w hw
    apply quotientEnvelopingMap_injective R S c
    rw [hzlog, ← hw, IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap R S c w)]

/-- The finite logarithm of an exponential product belongs to the canonical Lie image. -/
theorem log_exp_product_mem_range_quotientEnvelopingMap (c : ℕ) (x y : F) :
    IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι R x)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι R y))) ∈ (quotientEnvelopingMap R S c).range := by
  obtain ⟨a, ha, hred, himage, _⟩ := exists_primitive_representative_log_exp_product R S c x y
  rw [← himage]
  exact quotient_mem_range_quotientEnvelopingMap_of_reducedComul_mem R S c ha hred

local notation "F₂" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "U₂" => _root_.UniversalEnvelopingAlgebra ℚ F₂
local notation "J₂" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation ℚ U₂)
local notation "X" => _root_.FreeLieAlgebra.of ℚ (0 : Fin 2)
local notation "Y" => _root_.FreeLieAlgebra.of ℚ (1 : Fin 2)

/-- The universal finite BCH element in the two-generator free nilpotent Lie algebra. -/
noncomputable def bchElement (c : ℕ) :
    F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c :=
  Classical.choose (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp ℚ (Fin 2) c X Y)

/-- The universal BCH element exponentiates to the ordered product of generator exponentials. -/
theorem exp_quotientEnvelopingMap_bchElement (c : ℕ) :
    IsNilpotent.exp (quotientEnvelopingMap ℚ (Fin 2) c (bchElement c)) =
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) :=
  (Classical.choose_spec
    (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp ℚ (Fin 2) c X Y)).1

/-- The canonical image of the universal BCH element is the finite logarithm of the product. -/
theorem quotientEnvelopingMap_bchElement (c : ℕ) :
    quotientEnvelopingMap ℚ (Fin 2) c (bchElement c) =
      IsNilpotent.log (IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y))) := by
  rw [← exp_quotientEnvelopingMap_bchElement,
    IsNilpotent.log_exp (isNilpotent_quotientEnvelopingMap ℚ (Fin 2) c (bchElement c))]

/-- The exponential identity uniquely characterizes the universal finite BCH element. -/
theorem bchElement_unique (c : ℕ)
    (z : F₂ ⧸ LieModule.lowerCentralSeries ℚ F₂ F₂ c)
    (hz : IsNilpotent.exp (quotientEnvelopingMap ℚ (Fin 2) c z) =
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ X)) *
      IsNilpotent.exp (Ideal.Quotient.mk (J₂ ^ (c + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ Y))) : z = bchElement c :=
  (Classical.choose_spec
    (existsUnique_exp_quotientEnvelopingMap_eq_exp_mul_exp ℚ (Fin 2) c X Y)).2 z hz

/-- Projecting the universal BCH element to any smaller nilpotency bound gives that bound's
universal BCH element. -/
@[simp]
theorem factor_bchElement {c d : ℕ} (h : c ≤ d) :
    LieIdeal.factor (LieModule.lowerCentralSeries ℚ F₂ F₂ d)
      (LieModule.lowerCentralSeries ℚ F₂ F₂ c)
      (LieModule.antitone_lowerCentralSeries ℚ F₂ F₂ h) (bchElement d) = bchElement c := by
  apply bchElement_unique
  rw [quotientEnvelopingMap_factor ℚ (Fin 2) h]
  let π : U₂ ⧸ J₂ ^ (d + 1) →+* U₂ ⧸ J₂ ^ (c + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
  have hnil (z : F₂) :
      IsNilpotent (Ideal.Quotient.mk (J₂ ^ (d + 1))
        (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) := by
    simpa only [quotientEnvelopingMap_mk] using
      isNilpotent_quotientEnvelopingMap ℚ (Fin 2) d (LieSubmodule.Quotient.mk z)
  simpa only [IsNilpotent.map_exp
      (isNilpotent_quotientEnvelopingMap ℚ (Fin 2) d (bchElement d)),
    map_mul, IsNilpotent.map_exp (hnil X), IsNilpotent.map_exp (hnil Y),
    π, Ideal.Quotient.factor_mk] using
    congrArg π (exp_quotientEnvelopingMap_bchElement d)

/-- At nilpotency bound one, the universal BCH element is the sum of the generators. -/
@[simp]
theorem bchElement_one :
    bchElement 1 = LieSubmodule.Quotient.mk (X + Y) := by
  symm
  apply bchElement_unique
  rw [quotientEnvelopingMap_mk, map_add, map_add]
  let q := Ideal.Quotient.mk (J₂ ^ 2)
  have hmem (z : F₂) : _root_.UniversalEnvelopingAlgebra.ι ℚ z ∈ J₂ := by
    simpa only [pow_one] using
      TauCeti.UniversalEnvelopingAlgebra.pow_ι_mem_augmentation_toIdeal ℚ F₂ z
        (by decide : 1 ≠ 0)
  have hmul (u v : F₂) :
      q (_root_.UniversalEnvelopingAlgebra.ι ℚ u) *
        q (_root_.UniversalEnvelopingAlgebra.ι ℚ v) = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Submodule.pow_succ,
      Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_mul] using Ideal.mul_mem_mul (hmem u) (hmem v)
  have hsquare (z : F₂) : (q (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) ^ 2 = 0 := by
    simpa only [pow_two] using hmul z z
  have hcomm : Commute (q (_root_.UniversalEnvelopingAlgebra.ι ℚ X))
      (q (_root_.UniversalEnvelopingAlgebra.ι ℚ Y)) :=
    (hmul X Y).trans (hmul Y X).symm
  exact IsNilpotent.exp_add_of_commute hcomm ⟨2, hsquare X⟩ ⟨2, hsquare Y⟩

end Mei.FreeLieAlgebra
