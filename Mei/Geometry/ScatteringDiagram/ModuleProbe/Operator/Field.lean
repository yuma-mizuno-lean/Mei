/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Operators
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.RelativeCompletion.Map
public import Mei.Algebra.Lie.Graded.Operators.Finite

/-!
# Linear incoming families of actual probe fields

An operator-valued probe field determines a linear map from its incoming parameter
module to the ordinary shifted coefficient quotient. Evaluation identifies this
map with the fields extracted from independently supplied relative completions
of the evaluated inputs. Thus the geometric completion construction, despite its
choices of supports and generic anchors, is linear in the incoming coefficient.

The parameter module is arbitrary. No basis, finite generation, injectivity of
evaluation, or full-hyperplane hypothesis on the base supports is used. The
comparison holds at every base-allowed endpoint, including endpoints excluded
from the generic locus of either probe diagram. Base transport acts on the
resulting linear maps by postcomposition.

We combine `GradedOperators.quotientEquiv` with coefficient naturality for actual
relative completions; neither fields nor completions are defined by weighted ray
sums. The operator-probe construction follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {Λ V E κ ι Γ : Type*} {R H M L : Type u}
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

local notation "𝒪" => GradedOperators.lieGrading (H := H) ℳ ℒ
local notation "ev" a => LieModuleHom.toLinearMap (GradedOperators.evalLieModuleHom ℳ ℒ a)
local notation "hev" a => fun q f hf => GradedOperators.evalLieModuleHom_mem ℳ ℒ a hf
local notation "F" => d.shiftedFiltration ℳ p

variable
  (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W) ι)
  (B : DirectedDiagram (d := d) h W κ)

/-- The actual operator probe field, regarded as a linear family of finite
ordinary coefficients. Its input is the original parameter module. -/
def operatorExtendedCoefficientField (k : ℕ) (hB : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    H →ₗ[R] (F).quotient k :=
  (GradedOperators.quotientEquiv (H := TrivialLieModule R L H) d ℳ p k
    (extendedCoefficientField d 𝒪 p ℒ W h h' P B k hB x)).comp
      (TrivialLieModule.equiv R L H).symm.toLinearMap

/-- Reading the operator field at one input is the quotient coefficient map
induced by evaluation of its homogeneous operators. -/
@[simp]
theorem operatorExtendedCoefficientField_apply (k : ℕ) (hB : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) (a : H) :
    operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k hB x a =
      d.quotientCoefficientMap 𝒪 ℳ p (ev a) (hev a) k
        (extendedCoefficientField d 𝒪 p ℒ W h h' P B k hB x) := by
  simp only [operatorExtendedCoefficientField, LinearMap.comp_apply,
    LinearEquiv.coe_coe, GradedOperators.evalLieModuleHom_toLinearMap]
  exact GradedOperators.quotientEquiv_apply d ℳ p k _
    ((TrivialLieModule.equiv R L H).symm a)

/-- Base transport carries the whole incoming linear family by postcomposition,
using the ordinary finite BCH action. -/
theorem operatorExtendedCoefficientField_eq_transport (k : ℕ) (hB : B.LevelConsistent k)
    (x y : WallComplement (fun c : B.active k => (B.wall c).support)) :
    operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k hB y =
      ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        (B.levelTransport k hB x y)).toLinearMap.comp
          (operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k hB x) := by
  ext a
  simp only [operatorExtendedCoefficientField, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [extendedCoefficientField_eq_transport d 𝒪 p ℒ W h h' P B k hB x y,
    GradedOperators.quotientEquiv_truncatedBCHAction]

variable {η η' : Type*} (α : H →ₗ[R] ℳ p)

/-- Evaluation of an actual operator completion agrees with any independently
constructed relative completion of the evaluated incoming coefficient. No
common probe arrangement or shared choice of completion is required. -/
theorem operatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W) ((κ ⊕ Unit) ⊕ η))
    (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d 𝒪 p ℒ)
      (baseSection d 𝒪 p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d 𝒪 p ℒ W hy)
      (cylinderQuotientDiagram d 𝒪 p ℒ W h h' B)
      (probeDiagram d 𝒪 p ℒ W h h' (GradedOperators.homogeneousFamily ℳ ℒ p α)) P)
    (a : H)
    (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ W) ((κ ⊕ Unit) ⊕ η'))
    (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
      (baseSection d ℳ p ℒ)
      (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ W hy)
      (cylinderQuotientDiagram d ℳ p ℒ W h h' B)
      (probeDiagram d ℳ p ℒ W h h' (α a)) P')
    (k : ℕ) (hB : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k hB x a =
      extendedCoefficientField d ℳ p ℒ W h h' P' B k hB x := by
  have ha : mappedProbeCoefficient 𝒪 ℳ p (ev a) (hev a)
      (GradedOperators.homogeneousFamily ℳ ℒ p α) = α a := by
    apply Subtype.ext
    simp only [coe_mappedProbeCoefficient, LieModuleHom.coe_toLinearMap,
      GradedOperators.evalLieModuleHom_homogeneousFamily]
  rw [← ha] at hP'
  rw [operatorExtendedCoefficientField_apply]
  exact map_extendedCoefficientField_of_isRelativeOutgoingCompletion
    d 𝒪 ℳ p ℒ W h h' (ev a) (hev a)
    (fun z f => LieModuleHom.map_lie (GradedOperators.evalLieModuleHom ℳ ℒ a) z f)
    B (GradedOperators.homogeneousFamily ℳ ℒ p α) P P' hP hP' k hB x

/-- For a consistent base and a free degree lattice, at each finite cutoff `k` and
allowed endpoint `x` there is exactly one linear map whose evaluation at `a` is the
extended coefficient field of every relative completion of the probe diagram
`α a`. The source module may be infinitely generated. -/
theorem existsUnique_extendedCoefficientField_linear [Module.Free ℤ Γ]
    (hB : B.Consistent) (k : ℕ)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    ∃! Φ : H →ₗ[R] (F).quotient k, ∀ (a : H) (η : Type)
      (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
        (wallSpaces d ℳ p ℒ W) ((κ ⊕ Unit) ⊕ η))
      (_ : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
        (baseSection d ℳ p ℒ)
        (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ W hy)
        (cylinderQuotientDiagram d ℳ p ℒ W h h' B)
        (probeDiagram d ℳ p ℒ W h h' (α a)) P'),
      Φ a = extendedCoefficientField d ℳ p ℒ W h h' P' B k
        ((B.consistent_iff.mp hB) k) x := by
  obtain ⟨η, _, P, hP, _, _⟩ := exists_isRelativeOutgoingCompletion_probe
    d (GradedOperators.lieGrading (H := H) ℳ ℒ) p ℒ W h h' hB
      (GradedOperators.homogeneousFamily ℳ ℒ p α)
  refine ⟨operatorExtendedCoefficientField d ℳ p ℒ W h h' P B k
    ((B.consistent_iff.mp hB) k) x, ?_, ?_⟩
  · intro a η' P' hP'
    exact operatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
      d ℳ p ℒ W h h' B α P hP a P' hP' k ((B.consistent_iff.mp hB) k) x
  · intro Φ hΦ
    ext a
    obtain ⟨η', _, P', hP', _, _⟩ :=
      exists_isRelativeOutgoingCompletion_probe d ℳ p ℒ W h h' hB (α a)
    exact (hΦ a η' P' hP').trans
      (operatorExtendedCoefficientField_eq_of_isRelativeOutgoingCompletion
        d ℳ p ℒ W h h' B α P hP a P' hP' k ((B.consistent_iff.mp hB) k) x).symm

end Mei.ModuleProbe
