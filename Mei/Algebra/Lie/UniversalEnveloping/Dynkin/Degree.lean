/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Antipode
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Basic
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Basic

/-!
# Dynkin operators modulo total Lie degree

The antipode and lifted grading derivations preserve total Lie degree. Their
tensor contraction therefore preserves the total tensor filtration. An element
whose reduced coproduct vanishes through a degree cutoff has equal Dynkin and
grading-derivation values through that cutoff. This is the filtered identity
used to recover Lie representatives of approximate primitives.

This extends the augmentation-power calculation in
`Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Filtration` to degree filtrations;
these filtrations need not be cofinal. It uses the homogeneous word spans and
Mathlib's antipode and tensor-product maps.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "S" => _root_.HopfAlgebraStruct.antipode R (A := U)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)
  (hneg : ∀ n, d n < 0 → ℒ n = ⊥)

local notation "F" => degreeFiltration ℒ d hneg

variable (φ : Γ →+ R)

local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L
  (LieDerivation.ofGrading ℒ φ)
local notation "T" => Ideal.tensorFiltration R
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d hneg))
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d hneg))

/-- Every lifted grading derivation preserves the integral degree filtration. -/
theorem euler_mem_degreeFiltration {k : ℕ} {a : U} (ha : a ∈ (F).ideal k) :
    (Y : Module.End R U) a ∈ (F).ideal k := by
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.mem_degreeIdeal_iff,
    Mei.DirectSum.mem_degreeTail_iff] at ha ⊢
  intro n hn
  rw [euler_component ℒ φ, ha n hn, smul_zero]

/-- Antipode-Euler contraction preserves total tensor order. -/
theorem dynkinContraction_mem_degreeFiltration {k : ℕ} {t : U ⊗[R] U} (ht : t ∈ T k) :
    LinearMap.mul' R U (TensorProduct.map S (Y : Module.End R U) t) ∈ (F).ideal k := by
  have hm : (T k).restrictScalars R ≤
      (((F).ideal k).restrictScalars R).comap
        ((LinearMap.mul' R U).comp (TensorProduct.map S (Y : Module.End R U))) := by
    rw [Ideal.tensorFiltration_restrictScalars]
    simp only [iSup_le_iff, Submodule.map₂_le]
    intro i j hij x hx y hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply, TensorProduct.mk_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact (F).antitone hij ((F).mul_mem
      (antipode_mem_degreeFiltration ℒ d hneg hx) (euler_mem_degreeFiltration ℒ d hneg φ hy))
  exact hm ht

/-- Approximate primitivity makes the Dynkin and Euler values agree to the same degree order. -/
theorem dynkinOperator_sub_mem_degreeFiltration {k : ℕ} {a : U}
    (ha : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T k) :
    Mei.HopfAlgebra.dynkinOperator Y a - (Y : Module.End R U) a ∈ (F).ideal k := by
  have h := dynkinContraction_mem_degreeFiltration ℒ d hneg φ ha
  simpa only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply,
    _root_.HopfAlgebra.antipode_one, TauCeti.derivationLieAlgebra.apply_one_eq_zero,
    one_mul, mul_zero, sub_zero, ← Mei.HopfAlgebra.dynkinOperator_apply] using h

end Mei.UniversalEnvelopingAlgebra
