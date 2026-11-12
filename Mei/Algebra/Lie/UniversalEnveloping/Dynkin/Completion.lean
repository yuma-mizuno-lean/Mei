/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Reconstruction

/-!
# Primitive elements of completed enveloping algebras

Over a commutative rational algebra, completed primitive elements are exactly
canonical images of completed Lie elements. This connects the finite Dynkin
reconstruction `exists_truncatedLieToU_eq_iff` with homogeneous assembly by
`mem_range_completedLieToU_iff`. No freeness or injectivity of the canonical
Lie map is needed. In particular, logarithms of completed group-like units
have completed Lie representatives.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra (degreeFiltration)

open TauCeti (PositiveDegrees IsPositiveGrading)

namespace Mei.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

/-- Over a commutative rational algebra, completed primitives are exactly the
canonical images of completed Lie elements. -/
theorem mem_range_completedLieToU_iff_isCompletedPrimitive (u : (F).completion) :
    u ∈ Set.range (completedLieToU d ℒ) ↔ IsCompletedPrimitive ℒ d.degree _ u := by
  symm
  constructor
  · intro hu
    rw [mem_range_completedLieToU_iff]
    intro k
    apply (exists_truncatedLieToU_eq_iff ℒ d k _).mpr
    constructor
    · rw [← completedCounit_eq_quotientCounit]
      exact hu.completedCounit_eq_zero ℒ d.degree _
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((F).projection k u)
      rw [← ha, quotientCoproduct_mk, TauCeti.AlgFiltration.quotientIncludeLeft_mk,
        TauCeti.AlgFiltration.quotientIncludeRight_mk]
      have hp := congrArg (((F).tensorProduct R (F)).projection k)
        ((isCompletedPrimitive_iff ℒ d.degree _ u).mp hu)
      rw [TauCeti.AlgFiltration.completedTensor_one_right,
        TauCeti.AlgFiltration.completedTensor_one_left] at hp
      simp only [projection_completedCoproduct, map_add,
        TauCeti.AlgFiltration.projection_includeLeftCompletion,
        TauCeti.AlgFiltration.projection_includeRightCompletion, ← ha,
        quotientCoproduct_mk, Ideal.Quotient.factor_mk,
        Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply] at hp
      rw [← map_add] at hp ⊢
      have hm := Ideal.Quotient.eq.mp hp
      rw [TauCeti.AlgFiltration.tensorProduct_ideal] at hm
      exact Ideal.Quotient.eq.mpr hm
  · rintro ⟨x, rfl⟩
    exact isCompletedPrimitive_completedLieToU d ℒ x

end Mei.UniversalEnvelopingAlgebra
