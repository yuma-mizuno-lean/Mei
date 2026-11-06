/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.CoefficientMap
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Coefficient naturality of probe fields

The coefficient field extracted from actual upward probe crossings commutes with
homogeneous equivariant linear coefficient maps. The target diagram can be any
representative equivalent to the coefficient image of the source diagram. No
injectivity is required: walls and their individual contributions may disappear.

The same laws compare extended fields at allowed endpoints and completed fields.
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
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d 𝒩 p ℒ H) η)

local notation "φ" => coefficientGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv
local notation "hφ" => coefficientGradedLieHom_mem_wall d ℳ 𝒩 p ℒ f hf hequiv H
local notation "fₖ" => PositiveDegrees.quotientCoefficientMap d ℳ 𝒩 p f hf

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- Coefficient maps preserve upward crossing labels of equivalent target representatives
on the common generic locus, including diagrams with different active wall indices. -/
theorem map_combinedLabel_of_levelEquivalent (k : ℕ)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1)) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d 𝒩 p ℒ H h h' D' k).IsGeneric Q) :
    ((φ).truncatedMap (k + 1) (by simp)).bchGroupMap
        (D.combinedLabel (k + 1) (Q, 0) (0, j 1)
          (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)) =
      D'.combinedLabel (k + 1) (Q, 0) (0, j 1)
        (regular_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ') := by
  let P := DirectedWall.Pushforward.ofFixedDegree (h := h.prod h') φ hφ
  obtain ⟨a, ha, ha'⟩ := ((D.eventually_exists_levelPathProduct_eq_combinedLabel
    (k + 1) (Q, 0) (0, j 1) (regular_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)
      (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ)).and
    (D'.eventually_exists_levelPathProduct_eq_combinedLabel
      (k + 1) (Q, 0) (0, j 1) (regular_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ')
      (vertical_transverse_of_isGeneric d 𝒩 p ℒ H h h' D' k Q hQ'))).exists
  obtain ⟨x, y, e, hx, hy, he⟩ := ha
  obtain ⟨x', y', e', hx', hy', he'⟩ := ha'
  have hEq : (D.pushforward P).LevelEquivalent D' (k + 1) := by
    simpa only [P, DirectedDiagram.pushforward_ofFixedDegree] using hDD'
  have hp := (DirectedDiagram.levelEquivalent_def _ _ _).mp hEq
    ((D.levelPathPushforward P (k + 1) (by simp [P])).mapPath e.toPath) e'.toPath
      (by simp [Quiver.Path.vertices_toPath, P, hx, hy, hx', hy'])
  rw [D.levelPathProduct_pushforward, he, he'] at hp
  simpa only [P, DirectedWall.Pushforward.ofFixedDegree_lieHom_truncatedMap] using hp

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The finite field commutes with coefficient changes, including noninjective
ones, on the common generic locus of arbitrary actual representatives. -/
theorem map_coefficientField (k : ℕ)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1)) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d 𝒩 p ℒ H h h' D' k).IsGeneric Q) :
    fₖ k (coefficientField d ℳ p ℒ H h h' D k Q hQ) =
      coefficientField d 𝒩 p ℒ H h h' D' k Q hQ' := by
  simp only [coefficientField_def, verticalCoefficient_def, map_neg]
  rw [← moduleQuotientProjection_coefficientGradedLieHom d ℳ 𝒩 p ℒ f hf hequiv,
    ← LieHom.log_bchGroupMap,
    map_combinedLabel_of_levelEquivalent d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' k hDD' Q hQ hQ']

variable (B : DirectedDiagram (d := d) h H κ)

/-- Extended fields are natural on every base-allowed endpoint. Both fields are
extracted from their own probe diagrams; the target may have fewer active walls. -/
theorem map_extendedCoefficientField (k : ℕ) (hBc : B.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1)) (hD' : D'.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hB' : (D'.map (chargeZeroGradedLieHom d 𝒩 p ℒ)
      (chargeZeroGradedLieHom_mem_wall d 𝒩 p ℒ H)).LevelEquivalent
      (cylinderDiagram d 𝒩 p ℒ H h h' B) k)
    (hDD' : (D.map φ hφ).LevelEquivalent D' (k + 1))
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    fₖ k (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x) =
      extendedCoefficientField d 𝒩 p ℒ H h h' D' B k hBc x := by
  let T := (coefficientArrangement d ℳ p ℒ H h h' D k).union
    (coefficientArrangement d 𝒩 p ℒ H h h' D' k)
  obtain ⟨zB, hzT⟩ := exists_generic_allowed (d := d) (ℒ := ℒ) (H := H)
    (h := h) (B := B) k T x
  obtain ⟨hz, hz'⟩ := ExceptionalArrangement.isGeneric_union.mp hzT
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBc hD hB x zB hz,
    extendedCoefficientField_eq_action d 𝒩 p ℒ H h h' D' B k hBc hD' hB' x zB hz',
    PositiveDegrees.quotientCoefficientMap_truncatedBCHAction d ℳ 𝒩 p ℒ f hf hequiv,
    map_coefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' k hDD' zB.val hz hz']

/-- The completed field commutes with coefficient maps for consistent probe diagrams
with the stated coefficient and base-cylinder equivalences. -/
theorem map_completedExtendedCoefficientField
    (hD : D.Consistent) (hD' : D'.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hB' : (D'.map (chargeZeroGradedLieHom d 𝒩 p ℒ)
      (chargeZeroGradedLieHom_mem_wall d 𝒩 p ℒ H)).Equivalent
      (cylinderDiagram d 𝒩 p ℒ H h h' B))
    (hDD' : (D.map φ hφ).Equivalent D') (x : B.Point) :
    PositiveDegrees.completionCoefficientMap d ℳ 𝒩 p f hf
        (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) =
      completedExtendedCoefficientField d 𝒩 p ℒ H h h' D' B hD' hBc hB' x := by
  apply (d.shiftedFiltration 𝒩 p).completion_ext
  intro k
  rw [PositiveDegrees.projection_completionCoefficientMap,
    projection_completedExtendedCoefficientField, projection_completedExtendedCoefficientField]
  exact map_extendedCoefficientField d ℳ 𝒩 p ℒ H h h' f hf hequiv D D' B k
    ((B.consistent_iff.mp hBc) k) ((D.consistent_iff.mp hD) (k + 1))
    ((D'.consistent_iff.mp hD') (k + 1))
    (((DirectedDiagram.equivalent_iff _ _).mp hB) k)
    (((DirectedDiagram.equivalent_iff _ _).mp hB') k)
    (((DirectedDiagram.equivalent_iff _ _).mp hDD') (k + 1)) (CommonWallComplement.projection k x)

end Mei.ModuleProbe
