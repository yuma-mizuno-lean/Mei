/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Operator.Field
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Map

/-!
# One generic locus for a linear family of actual ray sums

The probe/ray comparison for an operator-valued incoming coefficient gives one
finite family of exceptional arrangements for every input in its parameter
module. On their common generic locus, the actual operator probe field evaluates
to the ordinary actual weighted ray sum. The arrangement is chosen before the
input, with no finite-generation or injectivity requirement. In particular an
input may kill whole decorations or the entire incoming coefficient.

The ordinary ray sums use the original directed diagram and incoming source region.
All simultaneous and unchanged-degree encounters, zero spatial shifts, and the
whole incoming tail are retained under evaluation at every parameter.
The operator-probe argument follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {Λ V E κ η : Type*} {Γ : Type} {R H M L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ]
  [AddCommGroup H] [Module R H] [AddCommGroup M] [Module R M]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (W : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating W ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h W κ) (α : H →ₗ[R] ℳ p)

local notation "𝒪" => GradedOperators.lieGrading (H := H) ℳ ℒ
local notation "ev" a:max => LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a)
local notation "hev" a:max => fun q f hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf
local notation "input" => GradedOperators.homogeneousFamily ℳ ℒ p α

variable
  (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W) ((κ ⊕ Unit) ⊕ η))

/-- A single generic endpoint locus identifies the actual operator probe field
with actual ordinary ray sums for every incoming parameter simultaneously.
The finite homogeneous input represents the prescribed whole incoming operator.
No geometric recurrence or coefficient-uniform comparison is assumed. -/
theorem exists_operatorExtendedCoefficientField_eq_cutoffWallEventEvaluation
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d 𝒪 p ℒ)
      (baseSection d 𝒪 p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d 𝒪 p ℒ W hy)
      (cylinderQuotientDiagram d 𝒪 p ℒ W h h' B)
      (probeDiagram d 𝒪 p ℒ W h h' input) P)
    (K : ℕ) (hBc : B.LevelConsistent K)
    (b : (d.shiftedQuotientGrading 𝒪 p K).piece 0)
    (hb : d.shiftedQuotientComponent 𝒪 p p K (by simp) b = input) :
    ∃ A : d.cutoff K → ExceptionalArrangement V,
      ∀ Q, (∀ n, (A n).IsGeneric Q) →
        ∃ hQ : ∀ c : B.active K, Q ∉ (B.wall c).support,
          ∀ a : H, operatorExtendedCoefficientField d ℳ p ℒ W h h' P B K hBc ⟨Q, hQ⟩ a =
            cutoffWallEventEvaluation d ℳ p ℒ W h B K K (Nat.le_refl K)
              ⟨d.quotientCoefficientMap 𝒪 ℳ p (ev a) (hev a) K b,
                d.quotientCoefficientMap_mem_shiftedQuotientGrading
                  𝒪 ℳ p (ev a) (hev a) b.property⟩ univ Q := by
  -- Compare the operator probe with its actual rays before specializing by evaluation.
  have hcomp := hP.isOutgoingCompletion_initialDiagram
  obtain ⟨A, hA⟩ := exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
    d 𝒪 p ℒ W h h' B input P B hcomp.wall_inl K hBc
    ((P.consistent_iff.mp hcomp.consistent) (K + 1))
    ((DirectedDiagram.equivalent_iff _ _).mp
      (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
        d 𝒪 p ℒ W h h' B input P hP) K)
    (fun _ c _ _ => hcomp.outgoing_inr c) b hb
  refine ⟨A, fun Q hQ => ?_⟩
  obtain ⟨hallowed, heq⟩ := hA Q hQ
  refine ⟨hallowed, fun a => ?_⟩
  rw [operatorExtendedCoefficientField_apply, heq]
  exact map_cutoffWallEventEvaluation d 𝒪 ℳ p ℒ W h B (ev a) (hev a)
    (fun x f => LieModuleHom.map_lie (GradedOperators.evalLieModuleHom ℳ ℒ a) x f)
    K K (Nat.le_refl K) b univ Q

end Mei.ModuleProbe
