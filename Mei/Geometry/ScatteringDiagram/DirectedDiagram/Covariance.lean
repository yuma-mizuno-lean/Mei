/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness

/-!
# Consistency and outgoing completions under coordinate changes

Compatible spatial and algebraic coordinate changes preserve incomingness,
outgoingness and consistency. Hence the image of an outgoing completion of an
initial family is an outgoing completion of the transported initial family.
By uniqueness, every outgoing completion of the transported family is equivalent
to that image: forming the consistent outgoing completion commutes with coordinate
changes. Finite-order consistency and equivalence are treated in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance.Basic`.

The completions are those of Travis Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5),
Theorem 2.6; here we record their naturality under integral-affine and algebraic coordinate
changes. Translations, changes of the positive degree function, repeated indexed walls and
walls with zero spatial velocity are allowed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι κ : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (D : DirectedDiagram (d := d) h H ι) (F : DirectedDiagram (d := d) h H κ)
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

variable {D F e E hE}

section Completion

variable {ι₀ ι' κ' : Type*} {D₀ : ι₀ → DirectedWall (d := d) h H}

/-- The image of an outgoing completion is an outgoing completion of the transported
initial walls. -/
theorem IsOutgoingCompletion.image {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hD : IsOutgoingCompletion D₀ D) :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) where
  wall_inl j := by rw [image_wall, hD.wall_inl]
  outgoing_inr j := by
    rw [image_wall, DirectedWall.outgoing_image_iff]
    exact hD.outgoing_inr j
  consistent := hD.consistent.image

variable (e E hE) in
/-- A diagram is an outgoing completion exactly when its image is an outgoing completion
of the transported initial walls. -/
@[simp]
theorem isOutgoingCompletion_image_iff {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) ↔
      IsOutgoingCompletion D₀ D := by
  refine ⟨fun hD => ⟨fun j => ?_, fun j => ?_, ?_⟩, IsOutgoingCompletion.image⟩
  · apply (DirectedWall.imageEquiv e E hE).injective
    simpa only [DirectedWall.imageEquiv_apply, image_wall] using hD.wall_inl j
  · simpa only [image_wall, DirectedWall.outgoing_image_iff] using hD.outgoing_inr j
  · exact (consistent_image_iff e E hE).mp hD.consistent

/-- Outgoing completion commutes with coordinate changes: every outgoing completion of
the transported initial walls is equivalent to the image of any outgoing completion of
the original initial walls. -/
theorem IsOutgoingCompletion.equivalent_image {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {D' : DirectedDiagram (d := d') h' H' (ι₀ ⊕ κ')} (hD : IsOutgoingCompletion D₀ D)
    (hD' : IsOutgoingCompletion (fun j => (D₀ j).image e E hE) D') :
    D'.Equivalent (D.image e E hE) :=
  outgoingCompletion_unique hD' hD.image

end Completion

end Mei.DirectedDiagram
