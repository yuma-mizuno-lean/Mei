/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension.Equivalence
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension.Map

/-!
# Coefficient maps of actual relative probe completions

A homogeneous equivariant coefficient map carries the initial cylinder and probe
input to the input for the mapped coefficient. Outgoing-completion uniqueness
then compares any two independently supplied relative completions. This permits
zero and noninjective maps, whose images may lose active walls and pure birth
logarithms. The comparison supplies the diagram equivalence needed for finite
and completed coefficient-field naturality.
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι η κ : Type*} {M N L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M] [LieRingModule L N] [LieModule R L N]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (𝒩 : Γ → Submodule R N) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ 𝒩]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating H ℳ] [IsWallAnnihilating H 𝒩]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (f : M →ₗ[R] N) (hf : ∀ q, ℳ q ≤ (𝒩 q).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅x, f a⁆)

local notation "φ" => coefficientGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv
local notation "hφ" => coefficientGradedLieHom_mem_wall d ℳ 𝒩 p ℒ f hf hequiv H

/-- Coefficient changes fix the completed charge-zero inclusion. -/
theorem completedMap_coefficientGradedLieHom_baseGradedLieHom
    (g : d.completedBCHGroup ℒ) :
    (φ).completedMap ((baseGradedLieHom d ℳ p ℒ).completedMap g) =
      (baseGradedLieHom d 𝒩 p ℒ).completedMap g := by
  have hc := GradedLieHom.completedMap_eq_of_toLieHom_eq
    ((φ).comp (baseGradedLieHom d ℳ p ℒ)) (baseGradedLieHom d 𝒩 p ℒ)
    (by
      apply LieHom.ext
      intro x
      simpa only [GradedLieHom.toLieHom_comp, LieHom.comp_apply,
        GradedLieHom.coe_toLieHom, baseGradedLieHom_apply, coefficientGradedLieHom_apply,
        baseInclusion, LieAlgebra.SemiDirectSum.inr_eq_mk] using
        coefficientLieHom_baseInclusion d ℳ 𝒩 p ℒ f hf hequiv x)
  simpa only [GradedLieHom.completedMap_comp, MonoidHom.comp_apply] using
    DFunLike.congr_fun hc g

/-- A cylinder wall maps to the cylinder with the same base label. -/
@[simp]
theorem baseCylinder_map_coefficientGradedLieHom (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).map φ hφ =
      baseCylinder d 𝒩 p ℒ H h h' W := by
  apply DirectedWall.ext
  case label =>
    simpa only [DirectedWall.map_label, baseCylinder_label] using
      completedMap_coefficientGradedLieHom_baseGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv W.label
  all_goals simp

/-- The mapped homogeneous input, including a coefficient killed by the map. -/
def mappedProbeCoefficient (a : ℳ p) : 𝒩 p := ⟨f a, hf p a.property⟩

omit [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] in
/-- The mapped homogeneous coefficient retains its ambient linear-map value. -/
@[simp]
theorem coe_mappedProbeCoefficient (a : ℳ p) :
    (mappedProbeCoefficient ℳ 𝒩 p f hf a : N) = f a := by rfl

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- Mapping a probe wall applies the coefficient map to its input. -/
@[simp]
theorem probeWall_map_coefficientGradedLieHom (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).map φ hφ =
      probeWall d 𝒩 p ℒ H h h' (mappedProbeCoefficient ℳ 𝒩 p f hf a) := by
  apply DirectedWall.ext
  case normal => simp
  case ray => simp
  case support => simp
  rw [DirectedWall.map_label, probeWall_label, probeWall_label,
    GradedLieHom.completedMap_expToCompletion]
  congr 1
  rw [coefficientGradedLieHom_apply]
  simp only [moduleInclusion, LieAlgebra.SemiDirectSum.inl_eq_mk,
    coefficientLieHom_moduleInclusion]
  congr 1
  apply (moduleCoefficientsEquiv d 𝒩 p).injective
  simp only [moduleCoefficientsEquiv_coefficientMap, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [PositiveDegrees.coe_shiftedCoefficientMap, coe_mappedProbeCoefficient]

variable (B : DirectedDiagram (d := d) h H κ)

/-- The entire initial probe family commutes with coefficient changes. -/
@[simp]
theorem initialDiagram_map_coefficientGradedLieHom (a : ℳ p) :
    (initialDiagram d ℳ p ℒ H h h' B a).map φ hφ =
      initialDiagram d 𝒩 p ℒ H h h' B (mappedProbeCoefficient ℳ 𝒩 p f hf a) := by
  apply DirectedDiagram.ext
  funext j
  rcases j with j | j
  · simp [baseCylinder_map_coefficientGradedLieHom d ℳ 𝒩 p ℒ H h h' f hf hequiv]
  · simp [probeWall_map_coefficientGradedLieHom d ℳ 𝒩 p ℒ H h h' f hf hequiv]

variable {η' : Type*} (a : ℳ p)
  (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((κ ⊕ Unit) ⊕ η))
  (P' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d 𝒩 p ℒ H) ((κ ⊕ Unit) ⊕ η'))
  (hP : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d ℳ p ℒ)
    (baseSection d ℳ p ℒ)
    (fun _ _ _ hy => baseSection_mem_wallSpaces d ℳ p ℒ H hy)
    (cylinderQuotientDiagram d ℳ p ℒ H h h' B) (probeDiagram d ℳ p ℒ H h h' a) P)
  (hP' : DirectedDiagram.IsRelativeOutgoingCompletion (baseProjection d 𝒩 p ℒ)
    (baseSection d 𝒩 p ℒ)
    (fun _ _ _ hy => baseSection_mem_wallSpaces d 𝒩 p ℒ H hy)
    (cylinderQuotientDiagram d 𝒩 p ℒ H h h' B)
    (probeDiagram d 𝒩 p ℒ H h h' (mappedProbeCoefficient ℳ 𝒩 p f hf a)) P')

include hP hP' in
/-- Independently supplied relative completions commute with coefficient maps.
Outgoing-completion uniqueness allows mapped walls to vanish. -/
theorem map_equivalent_of_isRelativeOutgoingCompletion : (P.map φ hφ).Equivalent P' := by
  have hp := hP.isOutgoingCompletion_initialDiagram.map φ hφ
  have hw : (fun j => ((initialDiagram d ℳ p ℒ H h h' B a).wall j).map φ hφ) =
      (initialDiagram d 𝒩 p ℒ H h h' B (mappedProbeCoefficient ℳ 𝒩 p f hf a)).wall := by
    rw [← initialDiagram_map_coefficientGradedLieHom d ℳ 𝒩 p ℒ H h h' f hf hequiv B a]
    funext j
    exact (DirectedDiagram.map_wall _ _ _ _).symm
  rw [hw] at hp
  exact DirectedDiagram.outgoingCompletion_unique hp hP'.isOutgoingCompletion_initialDiagram

include hP hP' hequiv in
/-- The finite extended fields of actual relative completions commute with
coefficient maps at every allowed endpoint. -/
theorem map_extendedCoefficientField_of_isRelativeOutgoingCompletion
    (k : ℕ) (hBc : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    PositiveDegrees.quotientCoefficientMap d ℳ 𝒩 p f hf k
        (extendedCoefficientField d ℳ p ℒ H h h' P B k hBc x) =
      extendedCoefficientField d 𝒩 p ℒ H h h' P' B k hBc x := by
  exact map_extendedCoefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv P P' B k hBc
    ((P.consistent_iff.mp hP.isOutgoingCompletion.consistent) (k + 1))
    ((P'.consistent_iff.mp hP'.isOutgoingCompletion.consistent) (k + 1))
    ((DirectedDiagram.equivalent_iff _ _).mp
      (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
        d ℳ p ℒ H h h' B a P hP) k)
    ((DirectedDiagram.equivalent_iff _ _).mp
      (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
        d 𝒩 p ℒ H h h' B (mappedProbeCoefficient ℳ 𝒩 p f hf a) P' hP') k)
    ((DirectedDiagram.equivalent_iff _ _).mp
      (map_equivalent_of_isRelativeOutgoingCompletion d ℳ 𝒩 p ℒ H h h' f hf hequiv B a
        P P' hP hP') (k + 1)) x

include hequiv in
/-- Completed fields of arbitrary actual relative completions commute with
coefficient changes, without a separate diagram-equivalence hypothesis. -/
theorem map_completedExtendedCoefficientField_of_isRelativeOutgoingCompletion
    (hBc : B.Consistent) (x : B.Point) :
    PositiveDegrees.completionCoefficientMap d ℳ 𝒩 p f hf
        (completedExtendedCoefficientField d ℳ p ℒ H h h' P B
          hP.isOutgoingCompletion.consistent hBc
          (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
            d ℳ p ℒ H h h' B a P hP) x) =
      completedExtendedCoefficientField d 𝒩 p ℒ H h h' P' B
        hP'.isOutgoingCompletion.consistent hBc
        (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
          d 𝒩 p ℒ H h h' B (mappedProbeCoefficient ℳ 𝒩 p f hf a) P' hP') x := by
  exact map_completedExtendedCoefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv P P' B
    hP.isOutgoingCompletion.consistent hP'.isOutgoingCompletion.consistent hBc
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d ℳ p ℒ H h h' B a P hP)
    (map_chargeZeroGradedLieHom_equivalent_of_isRelativeOutgoingCompletion
      d 𝒩 p ℒ H h h' B (mappedProbeCoefficient ℳ 𝒩 p f hf a) P' hP')
    (map_equivalent_of_isRelativeOutgoingCompletion d ℳ 𝒩 p ℒ H h h' f hf hequiv B a
      P P' hP hP') x

end Mei.ModuleProbe
