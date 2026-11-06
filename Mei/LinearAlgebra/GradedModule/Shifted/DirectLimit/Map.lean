/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component
public import Mei.LinearAlgebra.GradedModule.Shifted.Map

/-!
# Degree-preserving maps of global shifted coefficients

A linear map preserving every homogeneous piece acts on the existing shifted
completions. These maps commute with support inclusions, hence descend through
Mathlib's module direct limit. The resulting map preserves each ambient
component, and is functorial without injectivity or a spanning hypothesis.
No family needs a decomposition for the map or its chart and functoriality laws.
Decompositions are used only by the component formulas.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M N P : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝓝 : Γ → Submodule R N)
  (f : M →ₗ[R] N) (hf : ∀ u, ℳ u ≤ (𝓝 u).comap f)

/-- The map of global coefficients induced by a degree-preserving linear map. -/
def shiftedDirectLimitMap : d.ShiftedDirectLimit ℳ →ₗ[R] d.ShiftedDirectLimit 𝓝 :=
  Module.DirectLimit.map
    (f := fun s t h => d.coefficientInclusion ℳ s t h)
    (f' := fun s t h => d.coefficientInclusion 𝓝 s t h)
    (fun s => d.completionCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf)
    (by
      intro s t h
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.comp_apply, coefficientInclusion_eq] using
        d.completionCoefficientMap_inclusion ℳ 𝓝 f hf
          (d.coefficientOrigin s) (d.coefficientOrigin t) (d.coefficientOrigin_sub_mem h) x)

/-- The global map restricts to the original completion map in every canonical chart. -/
@[simp]
theorem shiftedDirectLimitMap_toShiftedDirectLimit (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit 𝓝 s
        (d.completionCoefficientMap ℳ 𝓝 (d.coefficientOrigin s) f hf x) := by
  simp only [shiftedDirectLimitMap, toShiftedDirectLimit_apply,
    Module.DirectLimit.map_apply_of]

/-- The global map acts componentwise by its original linear map. -/
@[simp]
theorem coe_shiftedDirectLimitComponents_map [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition 𝓝]
    (x : d.ShiftedDirectLimit ℳ) (u : Γ) :
    (d.shiftedDirectLimitComponents 𝓝 (d.shiftedDirectLimitMap ℳ 𝓝 f hf x) u : N) =
      f (d.shiftedDirectLimitComponents ℳ x u) := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  simp only [shiftedDirectLimitMap_toShiftedDirectLimit,
    shiftedDirectLimitComponents_toShiftedDirectLimit,
    coe_shiftedHomogeneousComponent_completionCoefficientMap]

/-- Mapping commutes with any chosen containing chart, not only a canonical origin. -/
@[simp]
theorem shiftedDirectLimitMap_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedDirectLimitMap ℳ 𝓝 f hf (d.toShiftedDirectLimitOfChart ℳ p s hp x) =
      d.toShiftedDirectLimitOfChart 𝓝 p s hp (d.completionCoefficientMap ℳ 𝓝 p f hf x) := by
  rw [toShiftedDirectLimitOfChart_apply, shiftedDirectLimitMap_toShiftedDirectLimit,
    completionCoefficientMap_inclusion, ← toShiftedDirectLimitOfChart_apply]

/-- The identity linear map induces the identity on global coefficients. -/
@[simp]
theorem shiftedDirectLimitMap_id (x : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitMap ℳ ℳ LinearMap.id (fun _ => le_rfl) x = x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  have hi : d.shiftedCoefficientMap ℳ ℳ (d.coefficientOrigin s) LinearMap.id
      (fun _ => le_rfl) = LinearMap.id := by
    ext a
    simp only [coe_shiftedCoefficientMap, LinearMap.id_apply]
  rw [shiftedDirectLimitMap_toShiftedDirectLimit, completionCoefficientMap_eq_completionMap]
  simp only [hi, ModuleFiltration.completionMap_id, LinearMap.id_apply]

/-- Global coefficient maps preserve composition of degree-preserving linear maps. -/
theorem shiftedDirectLimitMap_comp (ℒ : Γ → Submodule R P)
    (g : N →ₗ[R] P) (hg : ∀ u, 𝓝 u ≤ (ℒ u).comap g) (x : d.ShiftedDirectLimit ℳ) :
    d.shiftedDirectLimitMap 𝓝 ℒ g hg (d.shiftedDirectLimitMap ℳ 𝓝 f hf x) =
      d.shiftedDirectLimitMap ℳ ℒ (g.comp f) (fun u _ ha => hg u (hf u ha)) x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  simp only [shiftedDirectLimitMap_toShiftedDirectLimit, completionCoefficientMap_comp]

end Mei.PositiveDegrees
