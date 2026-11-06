/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Operator.Basic
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion.Map

/-!
# Evaluating the probe coefficient of a homogeneous family

Evaluating the operator probe at an input `a : H` carries the homogeneous operator coefficient
`GradedOperators.homogeneousFamily ℳ ℒ p g` to the coefficient `g a` of `ℳ p`
(`mappedProbeCoefficient_evalLieModuleHom_homogeneousFamily`).
Taking `H = ℳ p` and `g = LinearMap.id` gives the tautological coefficient of the operator probe:
its evaluation at `b : ℳ p` is `b`. By the naturality of relative completions under coefficient
maps (`Mei.ModuleProbe.map_extendedCoefficientField_of_isRelativeOutgoingCompletion`), the
evaluation at `b` of the probe field of the tautological coefficient is then the probe field of
`b`, so one probe computes the fields of all incoming coefficients simultaneously.

The probe construction follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ : Type*} {M L H : Type u} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L] [LieRingModule L M]
  [LieModule R L M] [AddCommGroup H] [Module R H]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ]
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)

/-- The evaluation at `a` carries the homogeneous coefficient of a linear family `g` to the
coefficient `g a`. -/
@[simp]
theorem mappedProbeCoefficient_evalLieModuleHom_homogeneousFamily (g : H →ₗ[R] ℳ p) (a : H) :
    mappedProbeCoefficient (GradedOperators.lieGrading (H := H) ℳ ℒ) ℳ p
      (LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a))
      (fun _ _ hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf)
      (GradedOperators.homogeneousFamily ℳ ℒ p g) = g a :=
  Subtype.ext ((coe_mappedProbeCoefficient _ ℳ p _ _ _).trans
    (GradedOperators.evalLieModuleHom_homogeneousFamily ℳ ℒ p g a))

end Mei.ModuleProbe
