/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance

/-!
# Affine covariance of the scattering class

The canonical outgoing scattering class commutes with compatible integral affine
and graded Lie coordinate changes. Positive degree functions may change, so the
finite comparison uses the coordinate change's cutoff modulus. Full-hyperplane
input is preserved automatically, including the translated offsets.

This combines `DirectedDiagram.scat_spec`, `IsOutgoingCompletion.image` and
`outgoingCompletion_unique`. The underlying completion theorem is Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Theorem 2.6.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v

variable {Γ Γ' Λ Λ' R V V' : Type*} {L L' : Type v} {ι : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [DecidableEq Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (D : DirectedDiagram (d := d) h H ι)
  (hfull : ∀ j, ∃ a : ℝ,
    (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ']

/-- Forming the canonical outgoing scattering class commutes with coordinate changes. -/
theorem image_scat :
    Class.image e E hE (D.Scat hfull) =
      (D.image e E hE).Scat (D.image_fullHyperplane hfull e E hE) := by
  obtain ⟨η, F, hF, hcF⟩ := D.scat_spec hfull
  rw [hcF, Class.image_toClass]
  symm
  apply scat_eq_toClass
  have hinput : (D.image e E hE).wall = fun j => (D.wall j).image e E hE :=
    funext (image_wall D e E hE)
  rw [hinput]
  exact hF.image

/-- The order-`k` scattering class transforms using any source order covering the modulus. -/
theorem projection_image_scat (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    ((D.image e E hE).Scat (D.image_fullHyperplane hfull e E hE)).projection k =
      LevelClass.image e E hE k ha ((D.Scat hfull).projection a) := by
  rw [← D.image_scat hfull e E hE, Class.projection_image_of_le e E hE k ha]

end Mei.DirectedDiagram
