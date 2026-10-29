/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Group
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Projection
import Mathlib.Data.Finset.NoncommProd

/-!
# Combining module-wall coefficients

Module walls on distinct charge-one rays can meet the same vertical crossing.
Their combined label is the exponential of the signed sum of their homogeneous
coefficients, embedded in the completed shifted module. No common degree or ray
is required. The kernel equivalence extracts this combined coefficient, and its
finite projections recover exactly the retained coefficient sums.

The integer exponents record the signed crossings, including a reversed normal
or path. This algebraic calculation does not require a geometric enumeration of
simultaneous walls. It uses `moduleWallGroupEquiv`,
`completedModuleBCHInclusion_of` and Mathlib's `Finset.map_noncommProd`.
The probe interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ : Type*} {M L : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  [Algebra ℚ R]
  [AddCommMonoid Λ] {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ]

local notation "G" => PositiveDegrees.completedBCHGroup (positiveDegrees d p) (grading d ℳ p ℒ)
local notation "π" => completedBaseProjection d ℳ p ℒ
local notation "ι" => completedModuleBCHInclusion d ℳ p ℒ
local notation "F" => d.shiftedFiltration ℳ p

section Kernel

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The completed kernel equivalence extracts the canonical image of the
homogeneous coefficient of a module-ray label. -/
theorem completedKernelEquiv_moduleWallGroupEquiv (q : Γ) (hq : q - p ∈ d.monoid)
    (a : Multiplicative (shiftedGrading ℳ d.monoid p (q - p))) :
    completedKernelEquiv d ℳ p ℒ
      ⟨(moduleWallGroupEquiv d ℳ p ℒ H q hq a : G), by
        rw [MonoidHom.mem_ker, coe_moduleWallGroupEquiv, completedBaseProjection_expToCompletion]
        simp [moduleInclusion]⟩ = Multiplicative.ofAdd ((F).of a.toAdd.val) := by
  apply completedModuleBCHInclusion_injective d ℳ p ℒ
  rw [completedModuleBCHInclusion_completedKernelEquiv,
    completedModuleBCHInclusion_of, coe_moduleWallGroupEquiv]

end Kernel

variable {J : Type*} (s : Finset J) (q : J → Γ) (hq : ∀ j, q j - p ∈ d.monoid)
  (g : ∀ j, (wallSpaces d ℳ p ℒ H).wallGroup (moduleRay d p (q j) (hq j)) probeNormal)

/-- The completed coefficient of a finite signed family of module walls. Each
homogeneous coefficient is included in the same completed shifted module before
addition, so distinct degrees and coincident indexed walls retain their weights. -/
def combinedModuleCoefficient (ε : J → ℤ) : (F).completion :=
  ∑ j ∈ s, ε j • (F).of
    (((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).symm (g j)).toAdd.val)

/-- The combined coefficient is the signed sum of the included homogeneous coefficients. -/
theorem combinedModuleCoefficient_def (ε : J → ℤ) :
    combinedModuleCoefficient d ℳ p ℒ H s q hq g ε =
      ∑ j ∈ s, ε j • (F).of
        (((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).symm (g j)).toAdd.val) := (rfl)

/-- An empty family contributes zero coefficient. -/
@[simp]
theorem combinedModuleCoefficient_empty (ε : J → ℤ) :
    combinedModuleCoefficient d ℳ p ℒ H ∅ q hq g ε = 0 := by
  simp [combinedModuleCoefficient]

/-- Adding one new indexed wall adds its signed homogeneous coefficient. -/
@[simp]
theorem combinedModuleCoefficient_insert [DecidableEq J] (j : J) (hj : j ∉ s)
    (ε : J → ℤ) :
    combinedModuleCoefficient d ℳ p ℒ H (insert j s) q hq g ε =
      ε j • (F).of
        (((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).symm (g j)).toAdd.val) +
          combinedModuleCoefficient d ℳ p ℒ H s q hq g ε := by
  simp [combinedModuleCoefficient, Finset.sum_insert hj]

/-- Finite projections of the combined coefficient are the signed sums of the
homogeneous coefficients modulo the relative filtration. -/
@[simp]
theorem projection_combinedModuleCoefficient (ε : J → ℤ) (k : ℕ) :
    (F).projection k (combinedModuleCoefficient d ℳ p ℒ H s q hq g ε) =
      ∑ j ∈ s, ε j • (Submodule.Quotient.mk
        (((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).symm (g j)).toAdd.val) :
          (F).quotient k) := by
  simp [combinedModuleCoefficient]

/-- The combined coefficient exponentiates to the finite signed product of the
actual module-wall labels, independently of any ordering of simultaneous walls. -/
theorem noncommProd_moduleWallLabels (ε : J → ℤ) :
    s.noncommProd (fun j => (g j : G) ^ ε j)
        (fun j _ l _ _ =>
          ((wallSpaces d ℳ p ℒ H).commute_of_mem_wallGroup
            (g j).property (g l).property one_ne_zero one_ne_zero rfl).zpow_zpow (ε j) (ε l)) =
      ι (Multiplicative.ofAdd (combinedModuleCoefficient d ℳ p ℒ H s q hq g ε)) := by
  let a (j : J) := Multiplicative.ofAdd ((F).of
    (((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).symm (g j)).toAdd.val))
  have ha (j : J) : (g j : G) = ι (a j) := by
    rw [completedModuleBCHInclusion_of]
    exact congrArg Subtype.val
      ((moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j)).apply_symm_apply (g j)) |>.symm.trans
        (coe_moduleWallGroupEquiv d ℳ p ℒ H (q j) (hq j) _)
  simp_rw [ha, ← map_zpow]
  rw [← Finset.map_noncommProd s (fun j => a j ^ ε j)
    (fun _ _ _ _ _ => Commute.all _ _) ι, Finset.noncommProd_eq_prod]
  simp only [combinedModuleCoefficient_def, ofAdd_sum, ofAdd_zsmul, a]

end Mei.ModuleProbe
