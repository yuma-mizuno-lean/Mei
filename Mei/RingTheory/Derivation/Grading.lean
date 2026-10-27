/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations from additive grading weights

An additive weight on the grading monoid defines a derivation that multiplies
each homogeneous element by its weight. Integer normal weights give the degree
derivations used to exponentiate function walls. The construction uses Mathlib's
`DirectSum.toModule` and `DirectSum.decomposeLinearEquiv`.
-/

public section

noncomputable section

namespace Mei.GradedAlgebra

open DirectSum

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

private def gradingLinearMap (φ : ι →+ R) : A →ₗ[R] A :=
  (DirectSum.toModule R ι A fun i => φ i • (𝒜 i).subtype).comp
    (decomposeLinearEquiv 𝒜).toLinearMap

private theorem gradingLinearMap_apply (φ : ι →+ R) {i : ι} {a : A}
    (ha : a ∈ 𝒜 i) : gradingLinearMap 𝒜 φ a = φ i • a := by
  simp [gradingLinearMap, decomposeLinearEquiv_apply, decompose_of_mem 𝒜 ha,
    ← lof_eq_of R]

/-- The derivation multiplying degree `i` by the additive weight `φ i`. -/
def gradingDerivation (φ : ι →+ R) : Derivation R A A where
  __ := gradingLinearMap 𝒜 φ
  map_one_eq_zero' := by
    rw [gradingLinearMap_apply 𝒜 φ SetLike.GradedOne.one_mem]
    simp
  leibniz' a b := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i a =>
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous j b =>
        rw [gradingLinearMap_apply 𝒜 φ (SetLike.GradedMul.mul_mem a.property b.property),
          gradingLinearMap_apply 𝒜 φ a.property, gradingLinearMap_apply 𝒜 φ b.property]
        simp only [map_add, smul_eq_mul, Algebra.smul_def]
        ring
      | add b c hb hc => simp only [mul_add, map_add, hb, hc, smul_eq_mul]; ring
    | add a b ha hb => simp only [add_mul, map_add, ha, hb, smul_eq_mul]; ring

/-- On a homogeneous element the grading derivation is scalar multiplication
by its weight. -/
theorem gradingDerivation_apply_of_mem (φ : ι →+ R) {i : ι} {a : A}
    (ha : a ∈ 𝒜 i) : gradingDerivation 𝒜 φ a = φ i • a :=
  gradingLinearMap_apply 𝒜 φ ha

/-- The grading derivation on a homogeneous element with degree in its type. -/
@[simp]
theorem gradingDerivation_apply (φ : ι →+ R) {i : ι} (a : 𝒜 i) :
    gradingDerivation 𝒜 φ a = φ i • (a : A) :=
  gradingDerivation_apply_of_mem 𝒜 φ a.property

end Mei.GradedAlgebra
