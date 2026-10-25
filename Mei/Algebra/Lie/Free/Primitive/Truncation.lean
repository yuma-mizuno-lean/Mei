/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Primitive.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Filtration

/-!
# Primitive detection modulo augmentation powers

In the enveloping algebra of a free Lie algebra over a commutative rational
algebra, an element of the augmentation ideal whose reduced coproduct has total
augmentation order at least `N` is congruent to a Lie element modulo `J ^ N`.
At order `c + 1`, its class lies in the image of the canonical map from the
free nilpotent Lie quotient.

The filtered Dynkin identity converts the coproduct defect into an Euler defect;
`exists_sub_ι_mem_augmentation_pow_of_dynkin_sub_mem` reconstructs the Lie element.
-/

public section

open scoped TensorProduct

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] [Algebra ℚ R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := F)
local notation "ℒ" => homogeneousSubmodule R S
local notation "E" => LieDerivation.ofGrading ℒ (Nat.castAddMonoidHom R)
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)
local notation "T" => Ideal.tensorFiltration R (fun n => J ^ n) (fun n => J ^ n)

/-- An element primitive up to total augmentation order `N` is a Lie element modulo `J ^ N`. -/
theorem exists_sub_ι_mem_augmentation_pow_of_reducedComul_mem {N : ℕ} {a : U}
    (ha : a ∈ J) (hred : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T N) :
    ∃ x : F, a - ι x ∈ J ^ N := by
  exact exists_sub_ι_mem_augmentation_pow_of_dynkin_sub_mem R S ha
    (Mei.UniversalEnvelopingAlgebra.dynkinOperator_sub_mem_augmentation_pow R F E hred)

/-- Approximate primitivity places the finite quotient class in the free nilpotent Lie image. -/
theorem quotient_mem_range_quotientEnvelopingMap_of_reducedComul_mem (c : ℕ) {a : U}
    (ha : a ∈ J)
    (hred : Coalgebra.comul (R := R) a - 1 ⊗ₜ[R] a - a ⊗ₜ[R] 1 ∈ T (c + 1)) :
    Ideal.Quotient.mk (J ^ (c + 1)) a ∈ (quotientEnvelopingMap R S c).range := by
  obtain ⟨x, hx⟩ := exists_sub_ι_mem_augmentation_pow_of_reducedComul_mem R S ha hred
  refine ⟨LieSubmodule.Quotient.mk x, ?_⟩
  rw [LieHom.coe_toLinearMap, quotientEnvelopingMap_mk]
  exact (Ideal.Quotient.eq.mpr hx).symm

end Mei.FreeLieAlgebra
