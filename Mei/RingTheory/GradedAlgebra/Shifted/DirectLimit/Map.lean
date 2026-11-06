/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Map
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Embedding

/-!
# Algebra maps of global shifted coefficients

A degree-preserving algebra homomorphism extends to the global coefficient
algebras for the same positive degrees. Multiplicativity is inherited from the
canonical naturality theorem for completed bilinear pairings. Multiplication is
already preserved by multiplicative linear maps between multiplicatively graded
decompositions, without unit preservation or graded-unit assumptions. The extension is
functorial and commutes with the finite coefficient embedding when positive
differences span the grading group. No injectivity of the algebra map is assumed.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A B C : Type*} [AddCommGroup Γ] [CommRing R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
  [DecidableEq Γ] (d : PositiveDegrees Γ)
  (𝒜 : Γ → Submodule R A) (ℬ : Γ → Submodule R B)

section Multiplicative

variable [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
  [SetLike.GradedMul 𝒜] [SetLike.GradedMul ℬ]
  (f : A →ₗ[R] B) (hf : ∀ u, 𝒜 u ≤ (ℬ u).comap f)
  (hmul : ∀ a b, f (a * b) = f a * f b)

include hmul in
/-- The descended linear map preserves global multiplication. -/
@[simp]
theorem shiftedDirectLimitMap_mul (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMap 𝒜 ℬ f hf (x * y) =
      d.shiftedDirectLimitMap 𝒜 ℬ f hf x *
        d.shiftedDirectLimitMap 𝒜 ℬ f hf y := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  obtain ⟨t, b, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
  rw [toShiftedDirectLimit_mul, shiftedDirectLimitMap_toShiftedDirectLimitOfChart,
    shiftedDirectLimitMap_toShiftedDirectLimit, shiftedDirectLimitMap_toShiftedDirectLimit,
    toShiftedDirectLimit_mul, completionCoefficientMap_mul d 𝒜 ℬ f hf hmul]

end Multiplicative

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : A →ₐ[R] B) (hf : ∀ u, 𝒜 u ≤ (ℬ u).comap f.toLinearMap)

/-- The descended linear map preserves the degree-zero algebra unit. -/
@[simp]
theorem shiftedDirectLimitMap_one :
    d.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf 1 = 1 := by
  apply d.shiftedDirectLimitComponents_injective ℬ
  funext u
  apply Subtype.ext
  rw [coe_shiftedDirectLimitComponents_map, shiftedDirectLimitComponents_one,
    shiftedDirectLimitComponents_one]
  have h := DirectSum.map_decompose_shift 𝒜 ℬ (f : A →+ B) id
    Function.injective_id (fun i a ha => hf i ha) u 1
  simpa only [AlgHom.coe_toAddMonoidHom, id_eq, AlgHom.toLinearMap_apply, map_one] using h

/-- Extend a degree-preserving algebra homomorphism to global shifted coefficients. -/
def shiftedDirectLimitAlgHom : d.ShiftedDirectLimit 𝒜 →ₐ[R] d.ShiftedDirectLimit ℬ :=
  AlgHom.ofLinearMap (d.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf)
    (d.shiftedDirectLimitMap_one 𝒜 ℬ f hf)
    (d.shiftedDirectLimitMap_mul 𝒜 ℬ f.toLinearMap hf f.map_mul)

/-- The global algebra homomorphism has the descended linear map as its underlying function. -/
theorem shiftedDirectLimitAlgHom_apply (x : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitAlgHom 𝒜 ℬ f hf x = d.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf x := by
  -- `AlgHom.ofLinearMap` retains its input linear map as the underlying function.
  rfl

/-- The extended algebra map applies the original map to every ambient component. -/
@[simp]
theorem coe_shiftedDirectLimitComponents_algHom (x : d.ShiftedDirectLimit 𝒜) (u : Γ) :
    (d.shiftedDirectLimitComponents ℬ (d.shiftedDirectLimitAlgHom 𝒜 ℬ f hf x) u : B) =
      f (d.shiftedDirectLimitComponents 𝒜 x u) := by
  rw [shiftedDirectLimitAlgHom_apply, coe_shiftedDirectLimitComponents_map,
    AlgHom.toLinearMap_apply]

/-- Extending the identity algebra homomorphism gives the identity. -/
@[simp]
theorem shiftedDirectLimitAlgHom_id :
    d.shiftedDirectLimitAlgHom 𝒜 𝒜 (AlgHom.id R A) (fun _ => le_rfl) =
      AlgHom.id R (d.ShiftedDirectLimit 𝒜) := by
  ext x
  exact d.shiftedDirectLimitMap_id 𝒜 x

/-- Extending a composition agrees with composing the global algebra maps. -/
theorem shiftedDirectLimitAlgHom_comp (𝒞 : Γ → Submodule R C) [GradedAlgebra 𝒞]
    (g : B →ₐ[R] C) (hg : ∀ u, ℬ u ≤ (𝒞 u).comap g.toLinearMap) :
    (d.shiftedDirectLimitAlgHom ℬ 𝒞 g hg).comp (d.shiftedDirectLimitAlgHom 𝒜 ℬ f hf) =
      d.shiftedDirectLimitAlgHom 𝒜 𝒞 (g.comp f) (fun u _ ha => hg u (hf u ha)) := by
  ext x
  exact d.shiftedDirectLimitMap_comp 𝒜 ℬ f.toLinearMap hf 𝒞 g.toLinearMap hg x

/-- Mapping an original finite coefficient agrees with mapping its global algebra image. -/
@[simp]
theorem shiftedDirectLimitAlgHom_toShiftedDirectLimitAlgHom
    (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b) (a : A) :
    d.shiftedDirectLimitAlgHom 𝒜 ℬ f hf (d.toShiftedDirectLimitAlgHom 𝒜 hspan a) =
      d.toShiftedDirectLimitAlgHom ℬ hspan (f a) := by
  apply d.shiftedDirectLimitComponents_injective ℬ
  funext u
  apply Subtype.ext
  rw [shiftedDirectLimitAlgHom_apply, coe_shiftedDirectLimitComponents_map,
    shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom,
    shiftedDirectLimitComponents_toShiftedDirectLimitAlgHom]
  exact DirectSum.map_decompose_shift 𝒜 ℬ f.toAddMonoidHom id Function.injective_id
    (fun i a ha => hf i ha) u a

end Mei.PositiveDegrees
