/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Derivation.Cocycle
public import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# Enveloping embeddings from injective Lie cocycles

An injective Lie derivation into a Lie module makes its sheared module a faithful
representation. Consequently the canonical map to the universal enveloping algebra
is injective. This criterion applies without freeness of the underlying module.

The representation is Tau Ceti's `LieDerivation.ShearedModule`: acting on the
vector corresponding to `(0, 1)` recovers the cocycle. The enveloping embedding
then follows from Mathlib's `UniversalEnvelopingAlgebra.lift`.
-/

public section

namespace LieDerivation

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- An injective cocycle gives a faithful representation on its sheared module. -/
theorem toEnd_shearedModule_injective (D : LieDerivation R L M)
    (hD : Function.Injective D) :
    Function.Injective (LieModule.toEnd R L D.ShearedModule) := by
  intro x y h
  have he := congrArg (fun f : Module.End R D.ShearedModule =>
    (ShearedModule.ofProd D).symm (f (ShearedModule.ofProd D (0, 1)))) h
  have hd : D x = D y := by
    simpa only [LieModule.toEnd_apply_apply, ShearedModule.ofProd_symm_lie,
      LinearEquiv.symm_apply_apply, lie_zero, one_smul, zero_add, Prod.mk.injEq,
      and_true] using he
  exact hD hd

/-- An injective Lie cocycle forces the canonical enveloping map to be injective. -/
theorem ι_injective_of_injective (D : LieDerivation R L M)
    (hD : Function.Injective D) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L) := by
  intro x y h
  apply D.toEnd_shearedModule_injective hD
  simpa only [UniversalEnvelopingAlgebra.lift_ι_apply] using
    congrArg (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L D.ShearedModule)) h

end LieDerivation
