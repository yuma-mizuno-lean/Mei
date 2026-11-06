/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Operator.Basic
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion.Map

/-!
# The tautological coefficient of an operator probe

Take the input module of the operator probe to be the coefficient piece `ℳ p` itself, with
the trivial Lie action. The identity of `ℳ p` is a homogeneous operator coefficient
`tautologicalCoefficient` of degree `p`, and its evaluation at `b : ℳ p` is `b`
(`evalLieModuleHom_tautologicalCoefficient`,
`mappedProbeCoefficient_evalLieModuleHom_tautologicalCoefficient`).
By the naturality of relative completions under coefficient maps
(`Mei.ModuleProbe.map_extendedCoefficientField_of_isRelativeOutgoingCompletion`), the evaluation
at `b` of the probe field of the tautological coefficient is then the probe field of `b`, so one
probe computes the fields of all incoming coefficients simultaneously.

The probe construction follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ : Type*} {M L : Type u} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L] [LieRingModule L M]
  [LieModule R L M] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ]
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)

local notation "ℳ'" => GradedOperators.lieGrading (H := ℳ p) ℳ ℒ
local notation "ev" => fun b : ℳ p =>
  LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ b)
local notation "hev" => fun (b : ℳ p) (q : Γ) (f) (hf : f ∈ ℳ' q) =>
  GradedOperators.evalLieModuleHom_mem ℳ ℒ b hf

/-- The identity of `ℳ p`, as a homogeneous operator coefficient of degree `p`. -/
def tautologicalCoefficient : ℳ' p :=
  GradedOperators.homogeneousFamily ℳ ℒ p LinearMap.id

/-- The evaluation at `b` carries the tautological coefficient to `b`. -/
@[simp↓]
theorem evalLieModuleHom_tautologicalCoefficient (b : ℳ p) :
    GradedOperators.evalLieModuleHom ℳ ℒ b (tautologicalCoefficient ℒ ℳ p) = (b : M) :=
  GradedOperators.evalLieModuleHom_homogeneousFamily ℳ ℒ p LinearMap.id b

/-- The evaluation at `b` carries the tautological coefficient to the coefficient `b`. -/
@[simp]
theorem mappedProbeCoefficient_evalLieModuleHom_tautologicalCoefficient (b : ℳ p) :
    mappedProbeCoefficient ℳ' ℳ p (ev b) (hev b) (tautologicalCoefficient ℒ ℳ p) = b :=
  Subtype.ext ((coe_mappedProbeCoefficient ℳ' ℳ p _ _ _).trans
    (evalLieModuleHom_tautologicalCoefficient ℒ ℳ p b))

end Mei.ModuleProbe
