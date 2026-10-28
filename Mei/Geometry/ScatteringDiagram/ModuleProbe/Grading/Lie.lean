/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Grading.Basic
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Degree
public import Mei.Algebra.Lie.Graded.Map

/-!
# Positive grading on the module probe

The semidirect bracket respects the extended degree: base elements have charge
zero, coefficients have charge one, and the bracket of two coefficients vanishes.
The original positive grading and the shifted support give a positive grading
for `ModuleProbe.positiveDegrees`, including coefficients of relative degree zero.
-/

public section
noncomputable section
namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

private theorem bracket_base_module {n q : Γ} {x : L}
    {a : shiftedSubmodule ℳ d.monoid p} (hx : x ∈ ℒ n)
    (ha : a ∈ shiftedGrading ℳ d.monoid p (q - p)) :
    ⁅baseInclusion d ℳ p ℒ x,
      moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a)⁆ ∈
      grading d ℳ p ℒ (n + q, 1, 0) := by
  rw [lie_baseInclusion_moduleInclusion, grading_module]
  refine Submodule.mem_map.mpr ⟨moduleCoefficientsEquiv d ℳ p
    (actionDerivationHom d ℳ p (ℒ := ℒ) x ((moduleCoefficientsEquiv d ℳ p).symm a)), ?_, ?_⟩
  · have h := actionDerivationHom_mem_shiftedGrading d ℳ p ℒ hx
      (a := (moduleCoefficientsEquiv d ℳ p).symm a)
      (by simpa only [LinearEquiv.apply_symm_apply] using ha)
    simpa only [add_sub_assoc] using h
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LieHom.coe_toLinearMap]

/-- The semidirect Lie bracket respects ambient degree and module charge. -/
instance instGradedBracketGrading [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (grading d ℳ p ℒ) (grading d ℳ p ℒ) where
  bracket_mem := by
    rintro ⟨n, c, l⟩ ⟨q, e, k⟩ x y hx hy
    by_cases h0 : c = 0 ∧ l = 0
    · rcases h0 with ⟨rfl, rfl⟩
      rw [grading_base] at hx
      by_cases h0' : e = 0 ∧ k = 0
      · rcases h0' with ⟨rfl, rfl⟩
        rw [grading_base] at hy
        let := (baseInclusion d ℳ p ℒ).gradedBracket_map ℒ
        simpa only [vadd_eq_add, Prod.mk_add_mk, zero_add, grading_base] using
          SetLike.GradedBracket.bracket_mem
            (ℒ := fun i => (ℒ i).map (baseInclusion d ℳ p ℒ).toLinearMap)
            (ℳ := fun i => (ℒ i).map (baseInclusion d ℳ p ℒ).toLinearMap) hx hy
      · rcases hx with ⟨x, hx, rfl⟩
        by_cases h1' : e = 1 ∧ k = 0
        · rcases h1' with ⟨rfl, rfl⟩
          rw [grading_module] at hy
          rcases hy with ⟨a, ha, rfl⟩
          exact bracket_base_module d ℳ p ℒ hx ha
        · have hy0 : y = 0 := by simpa only [grading_def, h0', h1', ↓reduceIte,
            Submodule.mem_bot] using hy
          rw [hy0, lie_zero]
          exact Submodule.zero_mem _
    · by_cases h1 : c = 1 ∧ l = 0
      · rcases h1 with ⟨rfl, rfl⟩
        rw [grading_module] at hx
        rcases hx with ⟨a, ha, rfl⟩
        by_cases h0' : e = 0 ∧ k = 0
        · rcases h0' with ⟨rfl, rfl⟩
          rw [grading_base] at hy
          rcases hy with ⟨y, hy, rfl⟩
          rw [← lie_skew]
          have h := (grading d ℳ p ℒ (q + n, 1, 0)).neg_mem
            (bracket_base_module d ℳ p ℒ hy ha)
          simpa only [vadd_eq_add, Prod.mk_add_mk, add_zero, zero_add, add_comm,
            LinearMap.comp_apply, LieHom.coe_toLinearMap, LinearEquiv.coe_toLinearMap] using h
        · by_cases h1' : e = 1 ∧ k = 0
          · rcases h1' with ⟨rfl, rfl⟩
            rw [grading_module] at hy
            rcases hy with ⟨b, hb, rfl⟩
            -- Reveal the two module inclusions hidden by the image linear maps.
            change ⁅moduleInclusion d ℳ p ℒ _, moduleInclusion d ℳ p ℒ _⁆ ∈ _
            rw [lie_moduleInclusion]
            exact Submodule.zero_mem _
          · have hy0 : y = 0 := by simpa only [grading_def, h0', h1', ↓reduceIte,
              Submodule.mem_bot] using hy
            rw [hy0, lie_zero]
            exact Submodule.zero_mem _
      · have hx0 : x = 0 := by simpa only [grading_def, h0, h1, ↓reduceIte,
          Submodule.mem_bot] using hx
        rw [hx0, zero_lie]
        exact Submodule.zero_mem _

variable [DirectSum.Decomposition ℳ]

/-- The module probe is graded by the ambient degree and two auxiliary coordinates. -/
instance instGradedLieAlgebraGrading [SetLike.GradedBracket ℒ ℒ] :
    GradedLieAlgebra (grading d ℳ p ℒ) where
  toDecomposition := inferInstance
  toGradedBracket := inferInstance

/-- Every nonzero probe component has nonzero allowed extended degree. -/
instance instIsPositiveGradingGrading :
    IsPositiveGrading (positiveDegrees d p) (grading d ℳ p ℒ) where
  eq_bot := by
    rintro ⟨q, c, l⟩ h
    by_cases h0 : c = 0 ∧ l = 0
    · rcases h0 with ⟨rfl, rfl⟩
      rw [grading_base, IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) q, Submodule.map_bot]
      simpa using h
    · by_cases h1 : c = 1 ∧ l = 0
      · rcases h1 with ⟨rfl, rfl⟩
        rw [grading_module, shiftedGrading_eq_bot ℳ d.monoid p, Submodule.map_bot]
        simpa using h
      · simp only [grading_def, h0, h1, ↓reduceIte]

end Mei.ModuleProbe
