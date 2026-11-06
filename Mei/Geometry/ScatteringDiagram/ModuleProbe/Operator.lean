/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Operators
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.CoefficientMap

/-!
# Evaluation of operator-valued module probes

Replace each homogeneous coefficient piece by the linear maps from an arbitrary
input module into that piece. Their uniformly finitely supported sum is a graded
Lie module under postcomposition. It inherits wall annihilation, so the ordinary
module-probe construction applies. Evaluation fixes the base Lie algebra and gives
a graded Lie map of probes preserving their directed wall spaces.

A homogeneous incoming linear family has a charge-one probe label; evaluation sends
it to the ordinary coefficient label, including when evaluation kills the coefficient.
Finite coefficient extraction commutes with this map. The operator module
retains entire homogeneous maps, including nonzero degree shifts whose spatial
projection vanishes.

The construction reuses `coefficientGradedLieHom` rather than rebuilding the semidirect
or quotient maps. Operator probes follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

universe u

section Evaluation

variable {R H M Γ L Λ : Type*} [CommRing R] [AddCommGroup H] [Module R H]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [AddCommMonoid Λ] {ρ : Γ →+ Λ}
  (W : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating W ℳ]

namespace ModuleProbe

local notation "𝒪" => GradedOperators.lieGrading (H := H) ℳ ℒ
local notation "ev" a => LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a)
local notation "hev" a => fun q f hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf

variable (p : Γ)

/-- Evaluate an operator-valued probe at one incoming coefficient. The base Lie
algebra is fixed, and the full charge-one coefficient is evaluated. -/
def operatorEvaluation (a : H) :
    GradedLieHom (PositiveDegreeMap.id (positiveDegrees d p))
      (grading d 𝒪 p ℒ) (grading d ℳ p ℒ) :=
  coefficientGradedLieHom d 𝒪 ℳ p ℒ (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie (GradedOperators.evalLieModuleHom ℳ ℒ a) x f)

/-- The operator probe's base summand is unchanged by evaluation. -/
@[simp↓]
theorem operatorEvaluation_baseInclusion (a : H) (x : L) :
    operatorEvaluation d ℳ ℒ p a (baseInclusion d 𝒪 p ℒ x) =
      baseInclusion d ℳ p ℒ x := by
  rw [operatorEvaluation, coefficientGradedLieHom_apply]
  exact coefficientLieHom_baseInclusion d 𝒪 ℳ p ℒ (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie _ x f) x

/-- Evaluation of the charge-one inclusion is the ordinary coefficient inclusion. -/
@[simp↓]
theorem operatorEvaluation_moduleInclusion (a : H) (f : ModuleCoefficients d 𝒪 p) :
    operatorEvaluation d ℳ ℒ p a (moduleInclusion d 𝒪 p ℒ f) =
      moduleInclusion d ℳ p ℒ (coefficientMap d 𝒪 ℳ p (ev a) (hev a) f) := by
  rw [operatorEvaluation, coefficientGradedLieHom_apply]
  exact coefficientLieHom_moduleInclusion d 𝒪 ℳ p ℒ (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie _ x f) f

/-- Evaluation preserves each reduced probe wall space, including zero evaluations. -/
theorem operatorEvaluation_mem_wall (a : H) (q : Γ × ℤ) (m : (Λ × ℤ) →+ ℤ)
    (x : ProbeLie d 𝒪 p ℒ) (hx : x ∈ (wallSpaces d 𝒪 p ℒ W).wall q m) :
    operatorEvaluation d ℳ ℒ p a x ∈ (wallSpaces d ℳ p ℒ W).wall q m :=
  coefficientGradedLieHom_mem_wall d 𝒪 ℳ p ℒ (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie _ x f) _ q m x hx

/-- Finite coefficient extraction commutes with evaluation of the probe. -/
@[simp]
theorem moduleQuotientProjection_operatorEvaluation (a : H) (k : ℕ)
    (x : (positiveDegrees d p).truncatedLie (grading d 𝒪 p ℒ) (k + 1)) :
    moduleQuotientProjection d ℳ p ℒ k
        ((operatorEvaluation d ℳ ℒ p a).truncatedMap (k + 1) (by simp) x) =
      d.quotientCoefficientMap 𝒪 ℳ p (ev a) (hev a) k
        (moduleQuotientProjection d 𝒪 p ℒ k x) :=
  moduleQuotientProjection_coefficientGradedLieHom d 𝒪 ℳ p ℒ (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie _ x f) k x

end ModuleProbe
end Evaluation

namespace ModuleProbe

section Completion

variable {R Γ : Type*} {H M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup H] [Module R H] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ)

local notation "𝒪" => GradedOperators.lieGrading (H := H) ℳ ℒ
local notation "ev" a => LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a)
local notation "hev" a => fun q f hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf

/-- Evaluation sends the exponential of an entire operator coefficient to the
exponential of its evaluated coefficient in the ordinary probe. -/
theorem operatorEvaluation_exp_moduleInclusion (a : H) (f : ModuleCoefficients d 𝒪 p) :
    (operatorEvaluation d ℳ ℒ p a).completedMap
        ((positiveDegrees d p).expToCompletion (grading d 𝒪 p ℒ)
          (moduleInclusion d 𝒪 p ℒ f)) =
      (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ (coefficientMap d 𝒪 ℳ p (ev a) (hev a) f)) := by
  rw [GradedLieHom.completedMap_expToCompletion, operatorEvaluation_moduleInclusion]

end Completion
end ModuleProbe
end Mei
