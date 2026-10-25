/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.HopfAlgebra.Dynkin
public import Mei.RingTheory.HopfAlgebra.Ideal
public import Mei.RingTheory.FilteredAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic

/-!
# Dynkin operators modulo augmentation powers

The antipode and every lifted Lie derivation preserve augmentation powers.
Their tensor contraction sends total augmentation order `N` into augmentation
order `N`. Consequently a primitive equation valid up to total order `N` implies
that the Dynkin operator and lifted derivation agree up to augmentation order `N`.

This uses `TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mem_stableDerivations_pow`
and the pure-tensor description of `Ideal.tensorFiltration`.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)
local notation "S" => _root_.HopfAlgebraStruct.antipode R (A := U)
local notation "T" => Ideal.tensorFiltration R (fun n => J ^ n) (fun n => J ^ n)

variable (D : LieDerivation R L L)

local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D

/-- Antipode-derivation contraction sends total augmentation order `N` to order `N`. -/
theorem dynkinContraction_mem_augmentation_pow {N : ℕ} {t : U ⊗[R] U} (ht : t ∈ T N) :
    LinearMap.mul' R U (TensorProduct.map S (Y : Module.End R U) t) ∈ J ^ N := by
  have hstable (n : ℕ) : Y ∈ TauCeti.stableDerivations R ((J ^ n).restrictScalars R) :=
    TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mem_stableDerivations_pow
      R L D J (fun x => TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation R L (D x)) n
  have hY (n : ℕ) {y : U} (hy : y ∈ J ^ n) : (Y : Module.End R U) y ∈ J ^ n :=
    (TauCeti.mem_stableDerivations R _ Y).mp (hstable n) y hy
  have hmap : (T N).restrictScalars R ≤
      ((J ^ N).restrictScalars R).comap
        ((LinearMap.mul' R U).comp (TensorProduct.map S (Y : Module.End R U))) := by
    rw [Ideal.tensorFiltration_restrictScalars]
    simp only [iSup_le_iff, Submodule.map₂_le]
    intro i j hij x hx y hy
    simp only [Submodule.mem_comap, LinearMap.comp_apply, TensorProduct.mk_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    apply Ideal.pow_le_pow_right hij
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul
      (Mei.HopfIdeal.antipode_mem_pow (TauCeti.HopfIdeal.augmentation R U) i hx) (hY j hy)
  exact hmap ht

/-- An approximate primitive equation makes Dynkin and the lifted derivation agree modulo
the corresponding augmentation power. -/
theorem dynkinOperator_sub_mem_augmentation_pow {N : ℕ} {a : U}
    (ha : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T N) :
    Mei.HopfAlgebra.dynkinOperator Y a - (Y : Module.End R U) a ∈ J ^ N := by
  have h := dynkinContraction_mem_augmentation_pow R L D ha
  simpa only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply,
    _root_.HopfAlgebra.antipode_one, TauCeti.derivationLieAlgebra.apply_one_eq_zero,
    one_mul, mul_zero, sub_zero, ← Mei.HopfAlgebra.dynkinOperator_apply] using h

end Mei.UniversalEnvelopingAlgebra
