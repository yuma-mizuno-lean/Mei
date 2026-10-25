/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Mei.RingTheory.HopfAlgebra.Dynkin
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.HopfAlgebra

/-!
# Dynkin operators in universal enveloping algebras

The Dynkin operator associated with any lifted Lie derivation has values in the canonical
Lie image. This supplies a Lie representative for the Dynkin value; in a positive
grading over a rational algebra, inverse Euler scaling then reconstructs primitive
elements in the Lie image. No basis, grading, or injectivity assumption is needed
for the Lie-image result itself.
-/

public section

open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieDerivation
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "U" => UniversalEnvelopingAlgebra R L
local notation "ι" => UniversalEnvelopingAlgebra.ι R

/-- The Dynkin operator of a lifted Lie derivation takes its values in the canonical Lie image. -/
theorem dynkinOperator_mem_range_ι (D : LieDerivation R L L) (a : U) :
    Mei.HopfAlgebra.dynkinOperator
      (TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D) a ∈
        (ι : L →ₗ⁅R⁆ U).toLinearMap.range := by
  let Y := TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L D
  let T := Mei.HopfAlgebra.dynkinOperator Y
  let P := (ι : L →ₗ⁅R⁆ U).toLinearMap.range
  have hprim (x : L) : Bialgebra.IsPrimitiveElem R (ι x) :=
    ⟨TauCeti.UniversalEnvelopingAlgebra.counit_ι R L x, by
      rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι]
      exact add_comm _ _⟩
  -- The strengthened statement handles arbitrary products in the algebra-generation induction.
  have hright (b : U) : ∀ a : U, T a ∈ P → T (a * b) ∈ P := by
    induction b using TauCeti.UniversalEnvelopingAlgebra.induction_ι R L with
    | «ι» x =>
      intro a ha
      obtain ⟨z, hz⟩ := ha
      rw [Mei.HopfAlgebra.dynkinOperator_mul_primitive Y a (hprim x),
        TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι, ← hz]
      refine ⟨⁅z, x⁆ + Coalgebra.counit (R := R) a • D x, ?_⟩
      simp only [LieHom.coe_toLinearMap, map_add, map_smul, LieHom.map_lie,
        LieRing.of_associative_ring_bracket]
    | algebraMap r =>
      intro a ha
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, map_smul]
      exact P.smul_mem r ha
    | add b c hb hc =>
      intro a ha
      rw [mul_add, map_add]
      exact P.add_mem (hb a ha) (hc a ha)
    | mul b c hb hc =>
      intro a ha
      rw [← mul_assoc]
      exact hc _ (hb _ ha)
  simpa only [one_mul] using hright a 1 (by
    rw [Mei.HopfAlgebra.dynkinOperator_one]
    exact P.zero_mem)

end LieDerivation
