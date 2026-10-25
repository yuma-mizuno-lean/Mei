/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Enveloping
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Grading
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Primitive elements in a free Lie enveloping algebra

The Euler derivation and its Dynkin operator detect the canonical Lie image without assuming
that homogeneous components of a primitive element are themselves primitive. The same
inverse-Euler calculation reconstructs Lie representatives modulo augmentation powers.
-/

public section

open scoped TensorProduct

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] (S : Type*)
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "ℒ" => homogeneousSubmodule R S
local notation "𝒰" => Mei.UniversalEnvelopingAlgebra.homogeneousSubmodule ℒ
local notation "E" => LieDerivation.ofGrading ℒ (Nat.castAddMonoidHom R)
local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R F E
local notation "T" => Mei.HopfAlgebra.dynkinOperator Y
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)

variable [Algebra ℚ R]

private noncomputable def inverseEuler : F →ₗ[R] F :=
  (DirectSum.toModule R ℕ F (fun n => (algebraMap ℚ R ((n : ℚ)⁻¹)) • (ℒ n).subtype)).comp
    (DirectSum.decomposeLinearEquiv ℒ).toLinearMap

private theorem inverseEuler_of_mem {n : ℕ} {x : F} (hx : x ∈ ℒ n) :
    inverseEuler R S x = (algebraMap ℚ R ((n : ℚ)⁻¹)) • x := by
  simp only [inverseEuler, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℒ hx,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof, LinearMap.smul_apply,
    Submodule.subtype_apply]

private theorem inverseEuler_component (x : F) (n : ℕ) :
    (DirectSum.decompose ℒ (inverseEuler R S x) n : F) =
      (algebraMap ℚ R ((n : ℚ)⁻¹)) • (DirectSum.decompose ℒ x n : F) := by
  have hhom (i : ℕ) (a : F) (ha : a ∈ ℒ i) : inverseEuler R S a ∈ ℒ i := by
    rw [inverseEuler_of_mem R S ha]
    exact (ℒ i).smul_mem _ ha
  have h := DirectSum.map_decompose_shift ℒ ℒ (inverseEuler R S).toAddMonoidHom
    (fun i => i) Function.injective_id hhom n x
  simp only [LinearMap.toAddMonoidHom_coe] at h
  rw [inverseEuler_of_mem R S (DirectSum.decompose ℒ x n).property] at h
  exact h.symm

private theorem ι_inverseEuler_component (x : F) (n : ℕ) :
    (DirectSum.decompose 𝒰 (_root_.UniversalEnvelopingAlgebra.ι R (inverseEuler R S x)) n : U) =
      (algebraMap ℚ R ((n : ℚ)⁻¹)) •
        (DirectSum.decompose 𝒰 (_root_.UniversalEnvelopingAlgebra.ι R x) n : U) := by
  rw [← Mei.UniversalEnvelopingAlgebra.ι_component, inverseEuler_component, map_smul,
    Mei.UniversalEnvelopingAlgebra.ι_component]

private theorem component_sub_inverseEuler_eq_zero (a : U) (x : F) (n : ℕ)
    (h0 : (DirectSum.decompose 𝒰 a 0 : U) = 0)
    (h : GradedAlgebra.proj 𝒰 n ((Y : Module.End R U) a -
      _root_.UniversalEnvelopingAlgebra.ι R x) = 0) :
    GradedAlgebra.proj 𝒰 n (a -
      _root_.UniversalEnvelopingAlgebra.ι R (inverseEuler R S x)) = 0 := by
  simp only [map_sub, GradedAlgebra.proj_apply,
    Mei.UniversalEnvelopingAlgebra.euler_component] at h
  simp only [map_sub, GradedAlgebra.proj_apply, ι_inverseEuler_component]
  by_cases hn : n = 0
  · subst n
    simp only [h0, Nat.cast_zero, inv_zero, map_zero, zero_smul, sub_self]
  · have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hc : (algebraMap ℚ R ((n : ℚ)⁻¹)) * (n : R) = 1 := by
      simpa only [map_mul, map_natCast, map_one] using
        congrArg (algebraMap ℚ R) (inv_mul_cancel₀ hq)
    rw [← sub_eq_zero.mp h, smul_smul, hc, one_smul, sub_self]

/-- An augmentation element whose Dynkin and Euler values agree through order `N` is
congruent to an actual free Lie element through the same order. -/
theorem exists_sub_ι_mem_augmentation_pow_of_dynkin_sub_mem {a : U} {N : ℕ}
    (ha : a ∈ J) (h : T a - (Y : Module.End R U) a ∈ J ^ N) :
    ∃ x : F, a - _root_.UniversalEnvelopingAlgebra.ι R x ∈ J ^ N := by
  obtain ⟨x, hx⟩ := (E).dynkinOperator_mem_range_ι a
  simp only [LieHom.coe_toLinearMap] at hx
  have h0 : (DirectSum.decompose 𝒰 a 0 : U) = 0 := by
    rw [Mei.UniversalEnvelopingAlgebra.component_zero_eq_counit ℒ
      (homogeneousSubmodule_zero R S)]
    have hc := (TauCeti.HopfIdeal.mem_augmentation R U).mp
      (TauCeti.HopfIdeal.mem_toIdeal.mp ha)
    simp only [hc, map_zero]
  refine ⟨inverseEuler R S x, (mem_augmentation_pow_iff R S _ N).mpr ?_⟩
  intro n hn
  have he : (Y : Module.End R U) a - _root_.UniversalEnvelopingAlgebra.ι R x ∈ J ^ N := by
    rw [hx]
    simpa only [neg_sub] using (J ^ N).neg_mem h
  have he0 := (mem_augmentation_pow_iff R S _ N).mp he n hn
  exact component_sub_inverseEuler_eq_zero R S a x n h0 he0

/-- The primitive elements in the enveloping algebra of a free Lie algebra over a rational
algebra are exactly its canonical Lie image. -/
theorem isPrimitiveElem_iff_mem_range_ι (a : U) :
    Bialgebra.IsPrimitiveElem R a ↔
      a ∈ (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap.range := by
  constructor
  · intro hp
    obtain ⟨x, hx⟩ := (E).dynkinOperator_mem_range_ι a
    simp only [LieHom.coe_toLinearMap] at hx
    have he : (Y : Module.End R U) a = _root_.UniversalEnvelopingAlgebra.ι R x := by
      rw [← Mei.HopfAlgebra.dynkinOperator_of_isPrimitiveElem Y hp]
      exact hx.symm
    have h0 : (DirectSum.decompose 𝒰 a 0 : U) = 0 := by
      rw [Mei.UniversalEnvelopingAlgebra.component_zero_eq_counit ℒ
        (homogeneousSubmodule_zero R S), hp.counit_eq_zero, map_zero]
    refine ⟨inverseEuler R S x, ?_⟩
    have hz : a - _root_.UniversalEnvelopingAlgebra.ι R (inverseEuler R S x) = 0 := by
      apply (DirectSum.decomposeLinearEquiv 𝒰).injective
      apply DirectSum.ext
      intro n
      apply Subtype.ext
      have hn := component_sub_inverseEuler_eq_zero R S a x n h0 (by
        simp only [he, sub_self, map_zero])
      simpa only [DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_zero,
        DirectSum.zero_apply, ZeroMemClass.coe_zero, GradedAlgebra.proj_apply] using hn
    exact (sub_eq_zero.mp hz).symm
  · rintro ⟨x, rfl⟩
    have hp : Bialgebra.IsPrimitiveElem R (_root_.UniversalEnvelopingAlgebra.ι R x) :=
      ⟨TauCeti.UniversalEnvelopingAlgebra.counit_ι R F x, by
        rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι]
        exact add_comm _ _⟩
    simpa only [LieHom.coe_toLinearMap] using hp

end Mei.FreeLieAlgebra
