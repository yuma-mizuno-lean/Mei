/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallSpace
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Ray

/-!
# Charge-one wall labels of module probes

At the probe normal, and hence at its nonzero multiples, the wall group on a charge-one
ray is the entire ray subgroup. It is therefore the additive homogeneous
coefficient group: every such wall label is the exponential of a unique
coefficient. Other normals give the trivial group, as does a charge-one
generator outside the shifted support, even if higher multiples are allowed.

These comparisons let combined probe wall labels be read as coefficients.
They use `ModuleProbe.moduleRayGroupEquiv`, `DirectedWallSpaces.wallGroup`
and Mathlib's `MulEquiv.subgroupCongr`. The module probe follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ Λ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ]

section

variable [DirectSum.Decomposition ℒ]

/-- Only the generator piece can contribute to a charge-one ray wall sum. -/
@[simp]
theorem raySubmodule_moduleRay (q : Γ) (hq : q - p ∈ d.monoid)
    (m : (Λ × ℤ × ℤ) →+ ℤ) :
    (wallSpaces d ℳ p ℒ H).raySubmodule (moduleRay d p q hq) m =
      (wallSpaces d ℳ p ℒ H).wall (q, 1, 0) m := by
  apply le_antisymm
  · rw [DirectedWallSpaces.raySubmodule_def]
    refine iSup_le fun a => ?_
    by_cases ha : (a : Γ × ℤ × ℤ) = (q, 1, 0)
    · simp only [ha, le_refl]
    · exact ((wallSpaces d ℳ p ℒ H).wall_le_piece a m).trans
        ((grading_eq_bot_of_charge_one_ray d ℳ p ℒ (moduleRay d p q hq)
          (moduleRay_generator d p q hq) a.property ha).le.trans bot_le)
  · exact (wallSpaces d ℳ p ℒ H).wall_le_raySubmodule _ m (by simp)

end

variable [GradedLieAlgebra ℒ] [DirectSum.Decomposition ℳ] [Algebra ℚ R]

/-- At the probe normal, the charge-one wall group exhausts the ray group. Nonzero
multiples of the normal reduce to this case by `DirectedWallSpaces.wallGroup_rescale`. -/
@[simp]
theorem wallGroup_moduleRay (q : Γ) (hq : q - p ∈ d.monoid) :
    (wallSpaces d ℳ p ℒ H).wallGroup (moduleRay d p q hq) probeNormal =
      (positiveDegrees d p).completedRaySubgroup (grading d ℳ p ℒ) (moduleRay d p q hq) := by
  apply DirectedWallSpaces.wallGroup_eq_completedRaySubgroup
  have h := wallSubmodule_module d ℳ p ℒ H q 1 one_ne_zero
  rw [one_smul] at h
  rw [raySubmodule_moduleRay, wallSpaces_wall, h, moduleRayLieSubalgebra_toSubmodule]

/-- Every other normal has trivial charge-one wall group. -/
theorem wallGroup_moduleRay_eq_bot_of_notMem_range (q : Γ) (hq : q - p ∈ d.monoid)
    (m : (Λ × ℤ × ℤ) →+ ℤ)
    (hm : m ∉ Set.range (fun c : ℤ => c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ))) :
    (wallSpaces d ℳ p ℒ H).wallGroup (moduleRay d p q hq) m = ⊥ := by
  apply DirectedWallSpaces.wallGroup_eq_bot_of_raySubmodule_eq_bot
  rw [raySubmodule_moduleRay, wallSpaces_wall]
  simp [wallSubmodule_def, hm]

/-- A charge-one ray outside the shifted support has no wall labels at any normal. -/
theorem wallGroup_eq_bot_of_notMem (w : SupportedRay (positiveDegrees d p))
    {q : Γ} (hw : w.generator = (q, 1, 0)) (hq : q - p ∉ d.monoid)
    (m : (Λ × ℤ × ℤ) →+ ℤ) :
    (wallSpaces d ℳ p ℒ H).wallGroup w m = ⊥ := by
  apply le_antisymm _ bot_le
  exact ((wallSpaces d ℳ p ℒ H).wallGroup_le_completedRaySubgroup w m).trans
    (completedRaySubgroup_eq_bot_of_notMem d ℳ p ℒ w hw hq).le

/-- Charge-one wall labels at the probe normal are exactly additive homogeneous
coefficients. -/
def moduleWallGroupEquiv (q : Γ) (hq : q - p ∈ d.monoid) :
    Multiplicative (shiftedGrading ℳ d.monoid p (q - p)) ≃*
      (wallSpaces d ℳ p ℒ H).wallGroup (moduleRay d p q hq) probeNormal :=
  (moduleRayGroupEquiv d ℳ p ℒ q hq).trans
    (MulEquiv.subgroupCongr (wallGroup_moduleRay d ℳ p ℒ H q hq).symm)

/-- The wall-group parametrization exponentiates the included coefficient. -/
@[simp]
theorem coe_moduleWallGroupEquiv (q : Γ) (hq : q - p ∈ d.monoid)
    (a : Multiplicative (shiftedGrading ℳ d.monoid p (q - p))) :
    (moduleWallGroupEquiv d ℳ p ℒ H q hq a :
      (positiveDegrees d p).completedBCHGroup (grading d ℳ p ℒ)) =
      (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm a.toAdd.val)) := by
  simp [moduleWallGroupEquiv]

/-- Recover a probe wall coefficient from its charge-one logarithmic component. -/
@[simp]
theorem coe_moduleWallGroupEquiv_symm (q : Γ) (hq : q - p ∈ d.monoid)
    (g : (wallSpaces d ℳ p ℒ H).wallGroup (moduleRay d p q hq) probeNormal) :
    (((moduleWallGroupEquiv d ℳ p ℒ H q hq).symm g).toAdd :
      shiftedSubmodule ℳ d.monoid p) =
      moduleCoefficientsEquiv d ℳ p
        ((positiveDegrees d p).logComponent (grading d ℳ p ℒ) g.val (q, 1, 0)).val.left := by
  simp [moduleWallGroupEquiv]

end Mei.ModuleProbe
