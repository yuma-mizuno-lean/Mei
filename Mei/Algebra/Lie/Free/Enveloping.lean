/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Quotient.Map
public import Mei.Algebra.Lie.Free.LowerCentral
public import Mei.Algebra.Lie.UniversalEnveloping.Cofinality
public import Mei.Algebra.Lie.UniversalEnveloping.GradedEmbedding
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Augmentation powers and the lower central series of a free Lie algebra

The degree-one free generators identify enveloping degree ideals with augmentation
powers. When the canonical enveloping map is injective, their preimages are exactly
the lower central series. The PBW embedding theorem supplies injectivity whenever
the underlying Lie module is free, in particular over every field.
The canonical map from the Lie quotient to the corresponding associative quotient exists
without that hypothesis; the kernel computation proves that it is injective under PBW.
-/

public section

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] (S : Type*)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "F" => _root_.FreeLieAlgebra R S
local notation "U" => _root_.UniversalEnvelopingAlgebra R F
local notation "ℒ" => homogeneousSubmodule R S
local notation "δ" => Nat.castAddMonoidHom ℤ
local notation "J" => TauCeti.HopfIdeal.toIdeal (TauCeti.HopfIdeal.augmentation R U)
local notation "𝓕" => Mei.UniversalEnvelopingAlgebra.degreeFiltration ℒ δ
  (fun n hn => False.elim (not_lt_of_ge (Int.natCast_nonneg n) hn))

/-- Word-length ideals of a free enveloping algebra are exactly augmentation powers. -/
theorem degreeFiltration_eq_augmentation_pow (k : ℕ) : (𝓕).ideal k = J ^ k := by
  have hpos : ∀ n, δ n ≤ 0 → ℒ n = ⊥ := by
    intro n hn
    have hn0 : n = 0 := by
      have hn' : (n : ℤ) ≤ 0 := hn
      omega
    subst n
    exact homogeneousSubmodule_zero R S
  apply le_antisymm
  · cases k with
    | zero => simp only [Mei.AlgFiltration.ideal_zero, Submodule.pow_zero, Ideal.one_eq_top, le_rfl]
    | succ k =>
      simpa only [Nat.add_sub_cancel, Nat.one_mul] using
        Mei.UniversalEnvelopingAlgebra.degreeFiltration_le_augmentation_pow
        ℒ δ (fun n hn => False.elim (not_lt_of_ge (Int.natCast_nonneg n) hn))
        (_root_.FreeLieAlgebra.of R : S → F) (fun _ => 1)
        (TauCeti.FreeLieAlgebra.lieSpan_range_of_eq_top R S)
        (fun s => by simpa using word_mem_homogeneousSubmodule R (FreeMagma.of s))
        1 (fun _ => le_rfl) (k + 1)
  · exact Mei.UniversalEnvelopingAlgebra.augmentation_pow_le_degreeFiltration ℒ δ hpos k

/-- Membership in an augmentation power is equivalent to vanishing of every lower
word-length component. -/
theorem mem_augmentation_pow_iff (a : U) (N : ℕ) :
    a ∈ J ^ N ↔ ∀ n : ℕ, (n : ℤ) < N →
      (DirectSum.decompose
        (Mei.UniversalEnvelopingAlgebra.homogeneousSubmodule ℒ) a n : U) = 0 := by
  rw [← degreeFiltration_eq_augmentation_pow R S N,
    Mei.UniversalEnvelopingAlgebra.degreeFiltration_ideal,
    Mei.GradedAlgebra.mem_degreeIdeal_iff, Mei.DirectSum.mem_degreeTail_iff]
  rfl

/-- The preimage of the `(c + 1)`-st augmentation power is the `c`-th lower central term. -/
theorem comap_augmentation_pow_ι
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    ((J ^ (c + 1)).restrictScalars R).comap
        (_root_.UniversalEnvelopingAlgebra.ι R : F →ₗ⁅R⁆ U).toLinearMap =
      (LieModule.lowerCentralSeries R F F c).toSubmodule := by
  rw [← degreeFiltration_eq_augmentation_pow R S (c + 1)]
  rw [Mei.UniversalEnvelopingAlgebra.comap_degreeFiltration_ι ℒ δ _
    hι]
  exact (lowerCentralSeries_toSubmodule_eq_degreeTail R (S := S) c).symm

private noncomputable def quotientEnvelopingHom (c : ℕ) : F →ₗ⁅R⁆ U ⧸ J ^ (c + 1) :=
  (Ideal.Quotient.mkₐ R (J ^ (c + 1))).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι R)

private theorem lowerCentralSeries_le_ker_quotientEnvelopingHom (c : ℕ) :
    LieModule.lowerCentralSeries R F F c ≤ (quotientEnvelopingHom R S c).ker := by
  intro x hx
  rw [LieHom.mem_ker, quotientEnvelopingHom, LieHom.comp_apply, AlgHom.toLieHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact TauCeti.UniversalEnvelopingAlgebra.ι_mem_augmentation_toIdeal_pow_of_mem_lowerCentralSeries
    R F hx

/-- The canonical map from a free nilpotent Lie quotient to the corresponding
augmentation quotient of its enveloping algebra. Its construction needs no PBW hypothesis. -/
noncomputable def quotientEnvelopingMap (c : ℕ) :
    (F ⧸ LieModule.lowerCentralSeries R F F c) →ₗ⁅R⁆ U ⧸ J ^ (c + 1) :=
  LieIdeal.liftQ (LieModule.lowerCentralSeries R F F c) (quotientEnvelopingHom R S c)
    (lowerCentralSeries_le_ker_quotientEnvelopingHom R S c)

/-- The quotient map sends the class of `x` to the class of its canonical enveloping image. -/
@[simp]
theorem quotientEnvelopingMap_mk (c : ℕ) (x : F) :
    quotientEnvelopingMap R S c (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk (J ^ (c + 1)) (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  rw [quotientEnvelopingMap, LieIdeal.liftQ_apply, quotientEnvelopingHom,
    LieHom.comp_apply, AlgHom.toLieHom_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- Every element of the canonical Lie image in the finite augmentation quotient is nilpotent. -/
theorem isNilpotent_quotientEnvelopingMap (c : ℕ)
    (z : F ⧸ LieModule.lowerCentralSeries R F F c) :
    IsNilpotent (quotientEnvelopingMap R S c z) := by
  obtain ⟨z, rfl⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries R F F c) z
  rw [LieIdeal.mkQ_apply, quotientEnvelopingMap_mk]
  refine ⟨c + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.pow_mem_pow
  simpa only [pow_one] using
    TauCeti.UniversalEnvelopingAlgebra.pow_ι_mem_augmentation_toIdeal R F z (by decide : 1 ≠ 0)

/-- The canonical enveloping maps commute with transitions to smaller nilpotency bounds. -/
theorem quotientEnvelopingMap_factor {c d : ℕ} (h : c ≤ d)
    (z : F ⧸ LieModule.lowerCentralSeries R F F d) :
    quotientEnvelopingMap R S c
        (LieIdeal.factor (LieModule.lowerCentralSeries R F F d)
          (LieModule.lowerCentralSeries R F F c)
          (LieModule.antitone_lowerCentralSeries R F F h) z) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
        (quotientEnvelopingMap R S d z) := by
  obtain ⟨z, rfl⟩ := LieIdeal.surjective_mkQ (LieModule.lowerCentralSeries R F F d) z
  simp only [LieIdeal.mkQ_apply, LieIdeal.factor_apply, quotientEnvelopingMap_mk,
    Ideal.Quotient.factor_mk]

private theorem ker_quotientEnvelopingHom
    (hι : Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R : F → U)) (c : ℕ) :
    (quotientEnvelopingHom R S c).ker = LieModule.lowerCentralSeries R F F c := by
  ext x
  rw [LieHom.mem_ker, quotientEnvelopingHom, LieHom.comp_apply, AlgHom.toLieHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact (SetLike.ext_iff.mp (comap_augmentation_pow_ι R S hι c)) x

/-- The free nilpotent Lie quotient embeds in the augmentation quotient whenever the
underlying free Lie module is free. In particular this applies over every field. -/
theorem quotientEnvelopingMap_injective [Module.Free R F] (c : ℕ) :
    Function.Injective (quotientEnvelopingMap R S c) := by
  rw [quotientEnvelopingMap]
  apply LieIdeal.liftQ_injective
  exact (ker_quotientEnvelopingHom R S (TauCeti.UniversalEnvelopingAlgebra.ι_injective R F) c).le

end Mei.FreeLieAlgebra
