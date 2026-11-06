/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Algebra.Lie.Graded.Operators.Basic
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Operator
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion.Map

/-!
# The tautological coefficient of an operator probe

Take the input module of the operator probe to be the coefficient piece `ℳ p` itself, with
the trivial Lie action. The identity of `ℳ p` is a homogeneous operator coefficient
`tautologicalCoefficient` of degree `p`, and its evaluation at `b : ℳ p` is `b`.
By the naturality of relative completions under coefficient maps, the evaluation at `b` of
the probe field of the tautological coefficient is the probe field of `b`, at every finite order
and after completion
(`quotientCoefficientMap_evalLieModuleHom_extendedCoefficientField_tautological`,
`completionCoefficientMap_evalLieModuleHom_completedExtendedCoefficientField_tautological`).
One probe thus computes the fields of all incoming coefficients simultaneously, as identities of
linear maps; the relative completions of the two probes are arbitrary and independent.

The probe and its coefficient maps are those of
`Mei.ModuleProbe.map_extendedCoefficientField_of_isRelativeOutgoingCompletion`. The probe
construction follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E η η' κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ] [AddCommGroup M] [Module R M]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)

local notation "ℳ'" => GradedOperators.lieGrading (H := ℳ p) ℳ ℒ
local notation "ev" => fun b : ℳ p =>
  LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ b)
local notation "hev" => fun (b : ℳ p) (q : Γ) (f) (hf : f ∈ ℳ' q) =>
  GradedOperators.evalLieModuleHom_mem ℳ ℒ b hf

/-- The identity of `ℳ p`, as a homogeneous operator coefficient of degree `p`. -/
def tautologicalCoefficient : ℳ' p :=
  GradedOperators.homogeneousFamily ℳ ℒ p LinearMap.id

omit [IsPositiveGrading d ℒ] [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The evaluation at `b` carries the tautological coefficient to the coefficient `b`. -/
theorem mappedProbeCoefficient_evalLieModuleHom_tautologicalCoefficient (b : ℳ p) :
    mappedProbeCoefficient ℳ' ℳ p (ev b) (hev b) (tautologicalCoefficient ℒ ℳ p) = b :=
  Subtype.ext ((coe_mappedProbeCoefficient ℳ' ℳ p _ _ _).trans
    (GradedOperators.evalLieModuleHom_homogeneousFamily ℳ ℒ p LinearMap.id b))

variable {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h H κ)

/-- Evaluation of a relative probe field of the tautological coefficient at `b` is the probe
field of `b`: the field of the operator module computes the fields of all incoming
coefficients simultaneously. The completions `P` and `P'` are arbitrary actual relative
completions of the two probes, independent of each other. -/
theorem quotientCoefficientMap_evalLieModuleHom_extendedCoefficientField_tautological
    (b : ℳ p)
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ' p ℒ H)
      ((κ ⊕ Unit) ⊕ η))
    (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
      ((κ ⊕ Unit) ⊕ η'))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ' p ℒ)
      (baseSection d ℳ' p ℒ) (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ' p ℒ H hy)
      (cylinderQuotientDiagram d ℳ' p ℒ H h h' B)
      (probeDiagram d ℳ' p ℒ H h h' (tautologicalCoefficient ℒ ℳ p)) P)
    (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ) (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' b) P')
    (k : ℕ) (hBc : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    PositiveDegrees.quotientCoefficientMap d ℳ' ℳ p (ev b) (hev b) k
        (extendedCoefficientField d ℳ' p ℒ H h h' P B k hBc x) =
      extendedCoefficientField d ℳ p ℒ H h h' P' B k hBc x :=
  map_extendedCoefficientField_of_isRelativeOutgoingCompletion d ℳ' ℳ p ℒ H h h'
    (ev b) (hev b)
    (fun x a => LieModuleHom.map_lie (GradedOperators.evalLieModuleHom ℳ ℒ b) x a) B
    (tautologicalCoefficient ℒ ℳ p) P P' hP (by
      rw [mappedProbeCoefficient_evalLieModuleHom_tautologicalCoefficient ℒ ℳ p]
      exact hP') k hBc x

/-- All-order version: evaluation of the completed field of the tautological coefficient at `b`
is the completed field of `b`, at every allowed endpoint of the base. -/
theorem completionCoefficientMap_evalLieModuleHom_completedExtendedCoefficientField_tautological
    (b : ℳ p)
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ' p ℒ H)
      ((κ ⊕ Unit) ⊕ η))
    (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
      ((κ ⊕ Unit) ⊕ η'))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ' p ℒ)
      (baseSection d ℳ' p ℒ) (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ' p ℒ H hy)
      (cylinderQuotientDiagram d ℳ' p ℒ H h h' B)
      (probeDiagram d ℳ' p ℒ H h h' (tautologicalCoefficient ℒ ℳ p)) P)
    (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ) (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
      (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' b) P')
    (hBc : B.Consistent) (x : B.Point) :
    PositiveDegrees.completionCoefficientMap d ℳ' ℳ p (ev b) (hev b)
        (completedExtendedCoefficientField d ℳ' p ℒ H h h' P B
          hP.isOutgoingCompletion.consistent hBc
          (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
            d ℳ' p ℒ H h h' B _ P hP) x) =
      completedExtendedCoefficientField d ℳ p ℒ H h h' P' B
        hP'.isOutgoingCompletion.consistent hBc
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d ℳ p ℒ H h h' B _ P' hP') x :=
  map_completedExtendedCoefficientField_of_isRelativeOutgoingCompletion d ℳ' ℳ p ℒ H h h'
    (ev b) (hev b)
    (fun x a => LieModuleHom.map_lie (GradedOperators.evalLieModuleHom ℳ ℒ b) x a) B
    (tautologicalCoefficient ℒ ℳ p) P P' hP (by
      rw [mappedProbeCoefficient_evalLieModuleHom_tautologicalCoefficient ℒ ℳ p]
      exact hP') hBc x

end Mei.ModuleProbe
