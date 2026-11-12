/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Consistency

/-!
# Consistency and equivalence under coordinate changes

Compatible spatial and algebraic coordinate changes preserve finite-order consistency
and finite-order equivalence of directed diagrams, with the cutoffs related by the
coordinate change's modulus: consistency or equivalence at a source cutoff covering the
modulus of a target order `k` gives the same property at `k`. In particular they
preserve and reflect consistency and equivalence at all orders.

These are the special case `DirectedWall.Pushforward.ofCoordinateChange` of
`DirectedDiagram.LevelConsistent.pushforward` and
`DirectedDiagram.LevelEquivalent.pushforward`.
Translations, changes of the positive degree function, repeated indexed walls and
walls with zero spatial velocity are allowed.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

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
  (e : TauCeti.Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

variable {D F e E hE}

/-- Consistency at a source cutoff covering the modulus of a target order gives
consistency of the transported diagram at that order. -/
theorem LevelConsistent.image {k a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a) : (D.image e E hE).LevelConsistent k := by
  rw [← pushforward_ofCoordinateChange]
  exact hD.pushforward (by rwa [DirectedWall.Pushforward.ofCoordinateChange_degreeMap])

/-- Coordinate changes preserve consistency at every order. -/
theorem Consistent.image (hD : D.Consistent) : (D.image e E hE).Consistent := by
  rw [← pushforward_ofCoordinateChange]
  exact hD.pushforward

variable (e E hE) in
/-- Coordinate changes preserve and reflect consistency. -/
@[simp]
theorem consistent_image_iff : (D.image e E hE).Consistent ↔ D.Consistent := by
  refine ⟨fun hD => ?_, Consistent.image⟩
  simpa using hD.image (e := e.symm) (E := E.symm) (hE := by simp [hE])

/-- Equivalence at a source cutoff covering the modulus of a target order gives
equivalence of the transported diagrams at that order. -/
theorem LevelEquivalent.image {k a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hDF : D.LevelEquivalent F a) :
    (D.image e E hE).LevelEquivalent (F.image e E hE) k := by
  rw [← pushforward_ofCoordinateChange, ← pushforward_ofCoordinateChange]
  exact hDF.pushforward (by rwa [DirectedWall.Pushforward.ofCoordinateChange_degreeMap])

/-- Coordinate changes preserve equivalence of directed diagrams. -/
theorem Equivalent.image (hDF : D.Equivalent F) :
    (D.image e E hE).Equivalent (F.image e E hE) := by
  rw [← pushforward_ofCoordinateChange, ← pushforward_ofCoordinateChange]
  exact hDF.pushforward

variable (e E hE) in
/-- Coordinate changes preserve and reflect equivalence of directed diagrams. -/
@[simp]
theorem equivalent_image_iff :
    (D.image e E hE).Equivalent (F.image e E hE) ↔ D.Equivalent F := by
  refine ⟨fun hDF => ?_, Equivalent.image⟩
  simpa using hDF.image (e := e.symm) (E := E.symm) (hE := by simp [hE])

end Mei.DirectedDiagram
