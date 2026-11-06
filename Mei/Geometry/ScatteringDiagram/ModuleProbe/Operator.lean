/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Postcomposition
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion.Map

/-!
# Probes with coefficients in a homomorphism module

For a module `X` on which the Lie algebra acts trivially, the linear maps `X → M` with finitely
many homogeneous components in total form a graded Lie module `Mei.gradedHom ℒ ℳ X`. Its
probe handles all incoming coefficients `φ v`, `v : X`, at once. The wall spaces annihilate its
pieces whenever they annihilate those of `M`, so the probe construction applies to it, and
evaluation at each `v : X` is a homogeneous equivariant coefficient map
(`Mei.gradedHomEval`, `Mei.gradedHomEval_mem`). The evaluations are jointly injective on every
finite-order coefficient quotient (`Mei.quotientGradedHomEval_injective`).

For `X = ℳ p` with the trivial action, the inclusion of `ℳ p` in `M` is a coefficient
`tautologicalCoefficient` of degree `p`, and evaluation at `b : ℳ p` sends it to `b`.
By the naturality of relative completions under coefficient maps, the evaluation at `b` of the
probe field of the tautological coefficient is the probe field of `b`, at every finite order and
after completion
(`quotientCoefficientMap_gradedHomEval_extendedCoefficientField_tautological`,
`completionCoefficientMap_gradedHomEval_completedExtendedCoefficientField_tautological`).
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

variable {R Γ Λ V E ι η η' κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ] [AddCommGroup M] [Module R M]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)

/-- The wall spaces annihilate the pieces of `gradedHom ℒ ℳ X` whenever they annihilate those
of `M`, because `L` acts on a map only through its values. -/
instance isWallAnnihilating_gradedHomPiece {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
    [IsWallAnnihilating H ℳ] (X : Type u) [AddCommGroup X] [Module R X] [LieRingModule L X]
    [LieModule R L X] [LieModule.IsTrivial L X] :
    IsWallAnnihilating H (gradedHomPiece ℒ ℳ X) where
  lie_eq_zero {_ _ _ _ _} hx ha hm := Subtype.ext (LinearMap.ext fun v => by
    simpa only [LieSubmodule.coe_bracket, lie_linearMap_apply, ZeroMemClass.coe_zero,
      LinearMap.zero_apply] using IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := ℳ) hx
        ((mem_gradedHomPiece ℒ ℳ X).mp ha v) hm)

variable {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h H κ)

local notation "ℳ'" => gradedHomPiece ℒ ℳ (TrivialLieModule R L (ℳ p))
local notation "ev" => fun b : ℳ p => gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b

omit [DirectSum.Decomposition ℳ] [IsPositiveGrading d ℒ] [Algebra ℚ R] [LieAlgebra ℚ L]
  [IsScalarTower ℚ R L] in
/-- The evaluation at `b` carries the tautological coefficient to the coefficient `b`. -/
theorem mappedProbeCoefficient_gradedHomEval_tautologicalCoefficient (b : ℳ p) :
    mappedProbeCoefficient ℳ' ℳ p (ev b).toLinearMap
      (fun _ _ ha => gradedHomEval_mem ℒ ℳ _ ha) (tautologicalCoefficient ℒ ℳ p) = b :=
  Subtype.ext ((coe_mappedProbeCoefficient ℳ' ℳ p _ _ _).trans
    (gradedHomEval_tautologicalCoefficient ℒ ℳ p b))

/-- Evaluation of a relative probe field of the tautological coefficient at `b` is the probe
field of `b`: the field of the homomorphism module computes the fields of all incoming
coefficients simultaneously. The completions `P` and `P'` are arbitrary actual relative
completions of the two probes, independent of each other. -/
theorem quotientCoefficientMap_gradedHomEval_extendedCoefficientField_tautological
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
    PositiveDegrees.quotientCoefficientMap d ℳ' ℳ p
        (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).toLinearMap
        (fun _ _ ha => gradedHomEval_mem ℒ ℳ _ ha) k
        (extendedCoefficientField d ℳ' p ℒ H h h' P B k hBc x) =
      extendedCoefficientField d ℳ p ℒ H h h' P' B k hBc x :=
  map_extendedCoefficientField_of_isRelativeOutgoingCompletion d ℳ' ℳ p ℒ H h h'
    (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).toLinearMap
    (fun _ _ ha => gradedHomEval_mem ℒ ℳ _ ha)
    (fun x a => (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).map_lie x a) B
    (tautologicalCoefficient ℒ ℳ p) P P' hP (by
      rw [mappedProbeCoefficient_gradedHomEval_tautologicalCoefficient ℒ ℳ p]
      exact hP') k hBc x

/-- All-order version: evaluation of the completed field of the tautological coefficient at `b`
is the completed field of `b`, at every allowed endpoint of the base. -/
theorem completionCoefficientMap_gradedHomEval_completedExtendedCoefficientField_tautological
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
    PositiveDegrees.completionCoefficientMap d ℳ' ℳ p
        (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).toLinearMap
        (fun _ _ ha => gradedHomEval_mem ℒ ℳ _ ha)
        (completedExtendedCoefficientField d ℳ' p ℒ H h h' P B
          hP.isOutgoingCompletion.consistent hBc
          (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
            d ℳ' p ℒ H h h' B _ P hP) x) =
      completedExtendedCoefficientField d ℳ p ℒ H h h' P' B
        hP'.isOutgoingCompletion.consistent hBc
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d ℳ p ℒ H h h' B _ P' hP') x :=
  map_completedExtendedCoefficientField_of_isRelativeOutgoingCompletion d ℳ' ℳ p ℒ H h h'
    (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).toLinearMap
    (fun _ _ ha => gradedHomEval_mem ℒ ℳ _ ha)
    (fun x a => (gradedHomEval ℒ ℳ (TrivialLieModule R L (ℳ p)) b).map_lie x a) B
    (tautologicalCoefficient ℒ ℳ p) P P' hP (by
      rw [mappedProbeCoefficient_gradedHomEval_tautologicalCoefficient ℒ ℳ p]
      exact hP') hBc x

end Mei.ModuleProbe
