/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Degree
public import Mei.Algebra.Lie.UniversalEnveloping.CompletedLie
import Mathlib.Algebra.Algebra.Rat

/-!
# Recovering Lie elements from degreewise primitive equations

Over a commutative rational algebra, an element in positive enveloping degree
whose reduced coproduct has total order at least `k` is congruent to a Lie
element modulo degree order `k`. No freeness, finite generation, or injectivity
of the canonical Lie map is required. The exact Dynkin-Euler identity likewise
recovers an exact Lie representative. For a positive grading, the image of the
finite canonical Lie map is precisely the zero-counit solutions of the primitive
equation in the total-degree tensor quotient.

The inverse-Euler calculation generalizes the word-length argument previously
in `Mei.Algebra.Lie.Free.Primitive.Basic`: divide the degree-`n` Dynkin value
by the nonzero integral weight `d n`. The zero-weight components vanish because
the input has positive degree. The Dynkin Lie-image theorem supplies a single
Lie element whose finitely many components can be rescaled.
-/

public section

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [DecidableEq Γ]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)
local notation "𝒰" => homogeneousSubmodule ℒ
local notation "F" => degreeFiltration ℒ d hneg
local notation "E" => LieDerivation.ofGrading ℒ (AddMonoidHom.comp (Int.castAddHom R) d)
local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L E
local notation "T" => Mei.HopfAlgebra.dynkinOperator Y

private noncomputable def inverseEuler : L →ₗ[R] L :=
  (DirectSum.toModule R Γ L (fun n => (algebraMap ℚ R ((d n : ℚ)⁻¹)) • (ℒ n).subtype)).comp
    (DirectSum.decomposeLinearEquiv ℒ).toLinearMap

private theorem inverseEuler_of_mem {n : Γ} {x : L} (hx : x ∈ ℒ n) :
    inverseEuler ℒ d x = (algebraMap ℚ R ((d n : ℚ)⁻¹)) • x := by
  simp only [inverseEuler, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem ℒ hx,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof, LinearMap.smul_apply,
    Submodule.subtype_apply]

private theorem inverseEuler_component (x : L) (n : Γ) :
    (DirectSum.decompose ℒ (inverseEuler ℒ d x) n : L) =
      (algebraMap ℚ R ((d n : ℚ)⁻¹)) • (DirectSum.decompose ℒ x n : L) := by
  have hhom (i : Γ) (a : L) (ha : a ∈ ℒ i) : inverseEuler ℒ d a ∈ ℒ i := by
    rw [inverseEuler_of_mem ℒ d ha]
    exact (ℒ i).smul_mem _ ha
  have h := DirectSum.map_decompose_shift ℒ ℒ (inverseEuler ℒ d).toAddMonoidHom
    (fun i => i) Function.injective_id hhom n x
  simp only [LinearMap.toAddMonoidHom_coe] at h
  rw [inverseEuler_of_mem ℒ d (DirectSum.decompose ℒ x n).property] at h
  exact h.symm

private theorem ι_inverseEuler_component (x : L) (n : Γ) :
    (DirectSum.decompose 𝒰 (ι (inverseEuler ℒ d x)) n : U) =
      (algebraMap ℚ R ((d n : ℚ)⁻¹)) • (DirectSum.decompose 𝒰 (ι x) n : U) := by
  rw [← ι_component, inverseEuler_component, map_smul, ι_component]

private theorem component_sub_inverseEuler_eq_zero (a : U) (x : L) (n : Γ)
    (h0 : d n = 0 → (DirectSum.decompose 𝒰 a n : U) = 0)
    (h : GradedAlgebra.proj 𝒰 n ((Y : Module.End R U) a - ι x) = 0) :
    GradedAlgebra.proj 𝒰 n (a - ι (inverseEuler ℒ d x)) = 0 := by
  simp only [map_sub, GradedAlgebra.proj_apply, euler_component,
    AddMonoidHom.comp_apply, Int.coe_castAddHom] at h
  simp only [map_sub, GradedAlgebra.proj_apply, ι_inverseEuler_component]
  by_cases hn : d n = 0
  · simp only [h0 hn, hn, Int.cast_zero, inv_zero, map_zero, zero_smul, sub_self]
  · have hq : (d n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hc : (algebraMap ℚ R ((d n : ℚ)⁻¹)) * (d n : R) = 1 := by
      simpa only [map_mul, map_intCast, map_one] using
        congrArg (algebraMap ℚ R) (inv_mul_cancel₀ hq)
    rw [← sub_eq_zero.mp h, smul_smul, hc, one_smul, sub_self]

/-- Equality of the Dynkin and Euler values through degree order `k` recovers a
Lie representative through that same order. -/
theorem exists_sub_ι_mem_degreeFiltration_of_dynkin_sub_mem {a : U} {k : ℕ}
    (ha : a ∈ (F).ideal 1) (h : T a - (Y : Module.End R U) a ∈ (F).ideal k) :
    ∃ x : L, a - ι x ∈ (F).ideal k := by
  obtain ⟨x, hx⟩ := (E).dynkinOperator_mem_range_ι a
  simp only [LieHom.coe_toLinearMap] at hx
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff,
    Mei.DirectSum.mem_degreeTail_iff] at ha
  refine ⟨inverseEuler ℒ d x, ?_⟩
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff,
    Mei.DirectSum.mem_degreeTail_iff]
  intro n hn
  apply component_sub_inverseEuler_eq_zero ℒ d a x n
    (fun hzero => ha n (by omega))
  have he : (Y : Module.End R U) a - ι x ∈ (F).ideal k := by
    rw [hx]
    simpa only [neg_sub] using ((F).ideal k).neg_mem h
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff,
    Mei.DirectSum.mem_degreeTail_iff] at he
  exact he n hn

/-- An exact Dynkin-Euler identity for a positive-degree element recovers an exact
Lie representative. -/
theorem exists_ι_eq_of_dynkin_eq {a : U} (ha : a ∈ (F).ideal 1)
    (h : T a = (Y : Module.End R U) a) : ∃ x : L, ι x = a := by
  obtain ⟨x, hx⟩ := (E).dynkinOperator_mem_range_ι a
  simp only [LieHom.coe_toLinearMap] at hx
  have he : (Y : Module.End R U) a = ι x := h.symm.trans hx.symm
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff,
    Mei.DirectSum.mem_degreeTail_iff] at ha
  refine ⟨inverseEuler ℒ d x, ?_⟩
  have hz : a - ι (inverseEuler ℒ d x) = 0 := by
    apply (DirectSum.decomposeLinearEquiv 𝒰).injective
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    have hn := component_sub_inverseEuler_eq_zero ℒ d a x n
      (fun hzero => ha n (by omega)) (by rw [he, sub_self, map_zero])
    simpa only [DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero, GradedAlgebra.proj_apply] using hn
  exact (sub_eq_zero.mp hz).symm

/-- An element primitive modulo total tensor order `k`, with positive degree, is
congruent to a Lie element modulo degree order `k`. -/
theorem exists_sub_ι_mem_degreeFiltration_of_reducedComul_mem {a : U} {k : ℕ}
    (ha : a ∈ (F).ideal 1)
    (hred : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈
      Ideal.tensorFiltration R (F).ideal (F).ideal k) :
    ∃ x : L, a - ι x ∈ (F).ideal k :=
  exists_sub_ι_mem_degreeFiltration_of_dynkin_sub_mem ℒ d hneg ha
    (dynkinOperator_sub_mem_degreeFiltration ℒ d hneg _ hred)

variable (p : PositiveDegrees Γ) [IsPositiveGrading p ℒ]

local notation "Fₚ" => degreeFiltration ℒ p.degree
  (fun n hn => p.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

/-- The finite canonical Lie image is characterized by zero counit and the primitive
identity in the total-degree tensor quotient. No coalgebra structure on the ordinary
quotient is required. -/
@[simp]
theorem exists_truncatedLieToU_eq_iff (k : ℕ) (z : U ⧸ (Fₚ).ideal (k + 1)) :
    (∃ x : p.truncatedLie ℒ k, truncatedLieToU p ℒ k x = z) ↔
      quotientCounit ℒ p.degree _ k z = 0 ∧
        quotientCoproduct ℒ p.degree _ (k + 1) z =
          Mei.AlgFiltration.quotientIncludeLeft R (Fₚ) (Fₚ) (k + 1) z +
            Mei.AlgFiltration.quotientIncludeRight R (Fₚ) (Fₚ) (k + 1) z := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (p.degreeIdeal ℒ k).surjective_mkQ x
    rw [LieIdeal.mkQ_apply, truncatedLieToU_mk]
    constructor
    · simp only [quotientCounit_mk, TauCeti.UniversalEnvelopingAlgebra.counit_ι]
    · simp only [quotientCoproduct_mk, Mei.AlgFiltration.quotientIncludeLeft_mk,
        Mei.AlgFiltration.quotientIncludeRight_mk,
        TauCeti.UniversalEnvelopingAlgebra.comul_ι, map_add]
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rintro ⟨hc, hp⟩
    rw [quotientCounit_mk] at hc
    have ha : a ∈ (Fₚ).ideal 1 :=
      augmentation_le_degreeFiltration_one ℒ p.degree
        (fun n hn => p.eq_bot_of_degree_nonpos ℒ n hn)
        ((TauCeti.HopfIdeal.mem_augmentation R U).mpr hc)
    have hred : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈
        Ideal.tensorFiltration R (Fₚ).ideal (Fₚ).ideal (k + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [quotientCoproduct_mk, Mei.AlgFiltration.quotientIncludeLeft_mk,
        Mei.AlgFiltration.quotientIncludeRight_mk] at hp
      simp only [map_sub]
      rw [hp]
      abel
    obtain ⟨x, hx⟩ := exists_sub_ι_mem_degreeFiltration_of_reducedComul_mem
      ℒ p.degree _ ha hred
    refine ⟨LieSubmodule.Quotient.mk x, ?_⟩
    rw [truncatedLieToU_mk]
    exact (Ideal.Quotient.eq.mpr hx).symm

end Mei.UniversalEnvelopingAlgebra
