/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.DegreeMap
public import Mei.RingTheory.GradedAlgebra.Shifted.DegreeMap
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Transport
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit

/-!
# Global algebra maps under changes of degrees

Multiplicative homogeneous coefficient maps preserve global shifted products,
including maps that merge degrees. Homogeneous units upgrade the resulting
linear maps to algebra homomorphisms. The product construction needs no unit
and no decomposition of the target algebra.

These are coefficient changes in the setting of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace TauCeti.PositiveDegreeMap

open Mei

variable {Γ Γ' R A B : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [DecidableEq Γ] [DecidableEq Γ'] {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  (T : PositiveDegreeMap d e) (𝒜 : Γ → Submodule R A) (ℬ : Γ' → Submodule R B)
  [DirectSum.Decomposition 𝒜]

section Multiplicative

variable [SetLike.GradedMul 𝒜] [SetLike.GradedMul ℬ]
  (f : A →ₗ[R] B) (hf : ∀ n, 𝒜 n ≤ (ℬ (T n)).comap f)

/-- Degree-changing global coefficient transport preserves products. -/
@[simp]
theorem shiftedDirectLimitMap_mul (hmul : ∀ a b, f (a * b) = f a * f b)
    (x y : d.ShiftedDirectLimit 𝒜) :
    T.shiftedDirectLimitMap 𝒜 ℬ f hf (x * y) =
      T.shiftedDirectLimitMap 𝒜 ℬ f hf x * T.shiftedDirectLimitMap 𝒜 ℬ f hf y :=
  d.shiftedDirectLimitMap_mul_of_charts e T.toAddMonoidHom (fun hn => T.map_mem hn)
    𝒜 ℬ (fun p => T.shiftedCompletionMap 𝒜 ℬ p f hf)
    (T.shiftedDirectLimitMap 𝒜 ℬ f hf)
    (T.shiftedDirectLimitMap_toShiftedDirectLimitOfChart 𝒜 ℬ f hf)
    (T.shiftedCompletionMap_mul 𝒜 ℬ f hf hmul) x y

end Multiplicative

variable [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ] [DirectSum.Decomposition ℬ]
  (f : A →ₐ[R] B) (hf : ∀ n, 𝒜 n ≤ (ℬ (T n)).comap f.toLinearMap)

/-- A degree-changing global algebra map preserves the homogeneous unit. -/
@[simp]
theorem shiftedDirectLimitMap_one : T.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf 1 = 1 := by
  let a : shiftedSubmodule 𝒜 d.monoid 0 := ⟨1, by
    have h : (1 : A) ∈ (supportedSubalgebra 𝒜 d.monoid).toSubmodule :=
      (supportedSubalgebra 𝒜 d.monoid).one_mem
    rwa [supportedSubalgebra_toSubmodule] at h⟩
  have ha : (a : A) = 1 := rfl
  have hzero' : T 0 - e.coefficientOrigin 0 ∈ e.monoid := by
    simpa only [T.map_zero] using e.zero_coefficientOrigin_mem
  rw [← d.toShiftedDirectLimitOfChart_of_eq_one 𝒜 0 0 d.zero_coefficientOrigin_mem a ha,
    T.shiftedDirectLimitMap_toShiftedDirectLimitOfChart 𝒜 ℬ f.toLinearMap hf
      0 0 d.zero_coefficientOrigin_mem 0 hzero', shiftedCompletionMap_of]
  apply e.toShiftedDirectLimitOfChart_of_eq_one
  simp only [coe_shiftedMap, AlgHom.toLinearMap_apply, ha, map_one]

/-- Extend a homogeneous algebra map along its degree map to global coefficients. -/
def shiftedDirectLimitAlgHom : d.ShiftedDirectLimit 𝒜 →ₐ[R] e.ShiftedDirectLimit ℬ :=
  AlgHom.ofLinearMap (T.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf)
    (T.shiftedDirectLimitMap_one 𝒜 ℬ f hf)
    (T.shiftedDirectLimitMap_mul 𝒜 ℬ f.toLinearMap hf f.map_mul)

/-- The algebra map retains the global linear map as its underlying function. -/
@[simp]
theorem shiftedDirectLimitAlgHom_apply (x : d.ShiftedDirectLimit 𝒜) :
    T.shiftedDirectLimitAlgHom 𝒜 ℬ f hf x = T.shiftedDirectLimitMap 𝒜 ℬ f.toLinearMap hf x := by
  -- `AlgHom.ofLinearMap` retains the input map's underlying function.
  rfl

/-- The identity degree and algebra maps induce the identity on global coefficients. -/
@[simp]
theorem shiftedDirectLimitAlgHom_id :
    (PositiveDegreeMap.id d).shiftedDirectLimitAlgHom 𝒜 𝒜 (AlgHom.id R A)
      (fun n => by simp) = AlgHom.id R (d.ShiftedDirectLimit 𝒜) := by
  ext x
  exact shiftedDirectLimitMap_id 𝒜 x

/-- Global algebra transport respects successive degree and coefficient changes. -/
theorem shiftedDirectLimitAlgHom_comp {Γ'' C : Type*} [AddCommGroup Γ''] [DecidableEq Γ'']
    [Ring C] [Algebra R C] {k : PositiveDegrees Γ''} (U : PositiveDegreeMap e k)
    (𝒞 : Γ'' → Submodule R C) [DirectSum.Decomposition 𝒞] [SetLike.GradedMonoid 𝒞]
    (g : B →ₐ[R] C) (hg : ∀ n, ℬ n ≤ (𝒞 (U n)).comap g.toLinearMap)
    (hc : ∀ n, 𝒜 n ≤ (𝒞 ((U.comp T) n)).comap (g.comp f).toLinearMap) :
    (U.shiftedDirectLimitAlgHom ℬ 𝒞 g hg).comp (T.shiftedDirectLimitAlgHom 𝒜 ℬ f hf) =
      (U.comp T).shiftedDirectLimitAlgHom 𝒜 𝒞 (g.comp f) hc := by
  ext x
  exact T.shiftedDirectLimitMap_comp 𝒜 ℬ f.toLinearMap hf U 𝒞 g.toLinearMap hg hc x

end TauCeti.PositiveDegreeMap
