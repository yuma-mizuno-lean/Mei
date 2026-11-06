/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Operator.Field

/-!
# Completed linear incoming families of probe fields

The finite linear families extracted from an operator probe assemble into a
linear map to the completed shifted coefficient module at every all-order
allowed endpoint. Evaluation agrees with every independently constructed
relative completion of the evaluated incoming coefficient. Thus neither the
completion choices nor the cutoff-dependent exceptional arrangements obstruct
linearity in the incoming parameter.

The parameter module is arbitrary, and no common open generic locus at all
orders is required. Base transport acts on the entire completed linear family
by postcomposition. These are completed probe fields; interpreting them as
global theta sections additionally requires the geometric local resolutions.

We use the finite operator-field comparison and the existing completion maps
and projections. The operator-probe interpretation follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {Λ V E κ ι : Type*} {R Γ H M L : Type u}
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

local notation "ev" a => LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a)
local notation "hev" a => fun q f hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf
local notation "F" => d.shiftedFiltration ℳ p

variable
  (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W) ι)
  (B : DirectedDiagram (d := d) h W κ)
  (hP : P.Consistent) (hB : B.Consistent)
  (hPB : (P.map (chargeZeroGradedLieHom d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ)
    (chargeZeroGradedLieHom_mem_wall d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W)).Equivalent
    (cylinderDiagram d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' B))

include hP hB hPB in
/-- The actual completed operator field as a linear family of ordinary
completed coefficients, characterized by its finite operator-field projections. -/
def completedOperatorExtendedCoefficientField (x : B.Point) : H →ₗ[R] (F).completion where
  toFun a := d.completionCoefficientMap (GradedOperators.lieGrading (H := H) ℳ ℒ) ℳ p (ev a) (hev a)
    (completedExtendedCoefficientField d (GradedOperators.lieGrading (H := H) ℳ ℒ)
      p ℒ W h h' P B hP hB hPB x)
  map_add' a b := by
    apply (F).completion_ext
    intro k
    simp only [map_add, PositiveDegrees.projection_completionCoefficientMap,
      projection_completedExtendedCoefficientField,
      ← operatorExtendedCoefficientField_apply d ℳ p ℒ W h h' P B]
  map_smul' c a := by
    apply (F).completion_ext
    intro k
    simp only [map_smul, PositiveDegrees.projection_completionCoefficientMap,
      projection_completedExtendedCoefficientField,
      ← operatorExtendedCoefficientField_apply d ℳ p ℒ W h h' P B, RingHom.id_apply]

/-- At every cutoff the completed linear family is exactly the independently
defined finite operator field, on the corresponding allowed endpoint. -/
@[simp]
theorem projection_completedOperatorExtendedCoefficientField (x : B.Point) (k : ℕ) (a : H) :
    (F).projection k
        (completedOperatorExtendedCoefficientField d ℳ p ℒ W h h' P B hP hB hPB x a) =
      operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k
        ((B.consistent_iff.mp hB) k) (CommonWallComplement.projection k x) a := by
  simp only [completedOperatorExtendedCoefficientField, LinearMap.coe_mk,
    AddHom.coe_mk, PositiveDegrees.projection_completionCoefficientMap,
    projection_completedExtendedCoefficientField, operatorExtendedCoefficientField_apply]

/-- Completed base transport carries the whole incoming linear family by
postcomposition with the completed BCH action. -/
theorem completedOperatorExtendedCoefficientField_eq_transport (x y : B.Point) :
    completedOperatorExtendedCoefficientField d ℳ p ℒ W h h' P B hP hB hPB y =
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ (B.transport hB x y)).toLinearMap.comp
        (completedOperatorExtendedCoefficientField d ℳ p ℒ W h h' P B hP hB hPB x) := by
  apply LinearMap.ext
  intro a
  apply (F).completion_ext
  intro k
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    ModuleFiltration.projection_completedBCHAction,
    projection_completedOperatorExtendedCoefficientField,
    B.projection_transport_eq_levelTransport]
  rw [projection_completedOperatorExtendedCoefficientField]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun
    (operatorExtendedCoefficientField_eq_transport d ℳ p ℒ W h h' P B k
      ((B.consistent_iff.mp hB) k) _ _) a

variable {η η' : Type*} (α : H →ₗ[R] ℳ p)

/-- Evaluating a completed operator probe agrees with any independent relative
completion of that input. Evaluation may kill coefficients and entire walls. -/
theorem completedOperatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W) ((κ ⊕ Unit) ⊕ η))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion
      (baseProjection d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ)
      (baseSection d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces
        d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W hy)
      (cylinderQuotientDiagram d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' B)
      (probeDiagram d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h'
        (GradedOperators.homogeneousFamily ℳ ℒ p α)) P)
    (a : H)
    (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ W) ((κ ⊕ Unit) ⊕ η'))
    (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ W hy)
      (cylinderQuotientDiagram d ℳ p ℒ W h h' B)
      (probeDiagram d ℳ p ℒ W h h' (α a)) P') (x : B.Point) :
    completedOperatorExtendedCoefficientField d ℳ p ℒ W h h' P B
        hP.isOutgoingCompletion.consistent hB
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' B
            (GradedOperators.homogeneousFamily ℳ ℒ p α) P hP) x a =
      completedExtendedCoefficientField d ℳ p ℒ W h h' P' B
        hP'.isOutgoingCompletion.consistent hB
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d ℳ p ℒ W h h' B (α a) P' hP') x := by
  apply (F).completion_ext
  intro k
  rw [projection_completedOperatorExtendedCoefficientField,
    projection_completedExtendedCoefficientField]
  exact operatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
    d ℳ p ℒ W h h' B α P hP a P' hP' k ((B.consistent_iff.mp hB) k) _

/-- A consistent base and free degree lattice determine one completed linear
incoming family at each all-order allowed endpoint. Its values agree with every
relative completion, without choosing compatible completions for different inputs. -/
theorem existsUnique_completedExtendedCoefficientField_linear [Module.Free ℤ Γ]
    (x : B.Point) :
    ∃! Φ : H →ₗ[R] (F).completion, ∀ (a : H) (η : Type)
      (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
        (wallSpaces d ℳ p ℒ W) ((κ ⊕ Unit) ⊕ η))
      (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
        (baseSection d ℳ p ℒ)
        (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ W hy)
        (cylinderQuotientDiagram d ℳ p ℒ W h h' B)
        (probeDiagram d ℳ p ℒ W h h' (α a)) P'),
      Φ a = completedExtendedCoefficientField d ℳ p ℒ W h h' P' B
        hP'.isOutgoingCompletion.consistent hB
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d ℳ p ℒ W h h' B (α a) P' hP') x := by
  obtain ⟨η, _, P, hP, _, _⟩ := exists_isRelativeOutgoingCompletion_probe
    d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' hB
      (GradedOperators.homogeneousFamily ℳ ℒ p α)
  let Φ := completedOperatorExtendedCoefficientField d ℳ p ℒ W h h' P B
    hP.isOutgoingCompletion.consistent hB
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' B
        (GradedOperators.homogeneousFamily ℳ ℒ p α) P hP) x
  have hΦ (a : H) (η' : Type)
      (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
        (wallSpaces d ℳ p ℒ W) ((κ ⊕ Unit) ⊕ η'))
      (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
        (baseSection d ℳ p ℒ)
        (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ W hy)
        (cylinderQuotientDiagram d ℳ p ℒ W h h' B)
        (probeDiagram d ℳ p ℒ W h h' (α a)) P') :=
    completedOperatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
      d ℳ p ℒ W h h' B hB α P hP a P' hP' x
  refine ⟨Φ, hΦ, fun Ψ hΨ => ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨η', _, P', hP', _, _⟩ :=
    exists_isRelativeOutgoingCompletion_probe d ℳ p ℒ W h h' hB (α a)
  exact (hΨ a η' P' hP').trans (hΦ a η' P' hP').symm

end Mei.ModuleProbe
