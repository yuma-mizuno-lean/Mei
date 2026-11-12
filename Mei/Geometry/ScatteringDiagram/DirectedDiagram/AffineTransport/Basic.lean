/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedWall.AffineTransport

/-!
# Affine transport of directed diagrams

Compatible spatial and algebraic coordinate changes transport a directed diagram,
preserving finite activity, incomingness and outgoingness. The degree functions
may differ.

Diagram transport is the pushforward along `DirectedWall.Pushforward.ofCoordinateChange`,
so paths and their products are transported by the pushforward path maps: at target
order `k`, from any source cutoff covering the coordinate change's modulus.
Repeated and coincident walls retain their indices; translations and
orientation-reversing affine equivalences are allowed.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' ι : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}
  (D : DirectedDiagram (d := d) h H ι)
  (e : TauCeti.Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Transport every indexed wall through compatible spatial and algebraic
coordinate changes. Finite activity is preserved through the cutoff modulus. -/
def image : DirectedDiagram (d := d') h' H' ι where
  wall j := (D.wall j).image e E hE
  finite_active := by
    simpa only [DirectedWall.image_label, E.completedEquiv_apply] using
      E.gradedLieHom.hasFiniteSupport_completedMap D.finite_active

/-- Diagram transport applies the existing affine transport to every wall. -/
@[simp]
theorem image_wall (j : ι) : (D.image e E hE).wall j = (D.wall j).image e E hE := (rfl)

/-- Coordinate changes of diagrams are pushforwards. -/
@[simp]
theorem pushforward_ofCoordinateChange :
    D.pushforward (DirectedWall.Pushforward.ofCoordinateChange e E hE) = D.image e E hE := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Integral affine transport preserves full-hyperplane inputs, with translated offsets. -/
theorem image_fullHyperplane
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    (e : TauCeti.Toric.IntegralAffineEquiv h h')
    (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
    (hE : E.tangentEquiv = e.latticeEquiv) : ∀ j, ∃ a : ℝ,
    ((D.image e E hE).wall j).support =
      {x | h'.realCharacter ((D.image e E hE).wall j).normal x = a} := by
  intro j
  obtain ⟨a, ha⟩ := hfull j
  rw [image_wall]
  exact ⟨_, (D.wall j).image_support_eq_hyperplane e E hE ha⟩

/-- Identity coordinates fix a directed diagram. -/
@[simp]
theorem image_refl :
    D.image (TauCeti.Toric.IntegralAffineEquiv.refl h)
      (DirectedWallSpaces.CoordinateChange.refl d H) (by simp) = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Successive spatial and algebraic coordinate changes compose on diagrams. -/
theorem image_image
    (f : TauCeti.Toric.IntegralAffineEquiv h' h'')
    (F : DirectedWallSpaces.CoordinateChange (d := d') (e := d'') H' H'')
    (hF : F.tangentEquiv = f.latticeEquiv) :
    (D.image e E hE).image f F hF =
      D.image (e.trans f) (E.trans F) (by simp [hE, hF]) := by
  apply DirectedDiagram.ext
  funext j
  simp only [image_wall, DirectedWall.image_image]

/-- Transport by the inverse coordinates recovers the original diagram. -/
@[simp]
theorem image_symm_image :
    (D.image e E hE).image e.symm E.symm (by simp [hE]) = D := by
  rw [image_image]
  simp

/-- Affine coordinate changes identify the existing directed-diagram carriers. -/
def imageEquiv : DirectedDiagram (d := d) h H ι ≃ DirectedDiagram (d := d') h' H' ι where
  toFun D := D.image e E hE
  invFun D := D.image e.symm E.symm (by simp [hE])
  left_inv D := D.image_symm_image e E hE
  right_inv D := by simpa using D.image_symm_image e.symm E.symm (by simp [hE])

@[simp]
theorem imageEquiv_apply : imageEquiv e E hE D = D.image e E hE := (rfl)

@[simp]
theorem imageEquiv_symm_apply (D' : DirectedDiagram (d := d') h' H' ι) :
    (imageEquiv (ι := ι) e E hE).symm D' = D'.image e.symm E.symm (by simp [hE]) := (rfl)

end Mei.DirectedDiagram
