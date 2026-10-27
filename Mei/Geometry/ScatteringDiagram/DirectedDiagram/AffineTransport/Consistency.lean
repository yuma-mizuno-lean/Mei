/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance

/-!
# Endpoint transport under coordinate changes

Finite and completed endpoint transports commute with integral affine changes of
spatial coordinates and compatible changes of the graded Lie data. The positive
degree functions may differ: a source cutoff covers the target cutoff through
the coordinate change's modulus.

Consistency and outgoing-completion preservation are supplied by
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Covariance`. The transport formulas
use its consistency results and the path-product comparisons from
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport.Basic`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι : Type*} {L L' : Type u}
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
  (D : DirectedDiagram (d := d) h H ι)
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Finite endpoint transport is natural at any source cutoff covering the
coordinate modulus. The target endpoints need only be images of the given
source endpoints. -/
@[simp]
theorem levelTransport_image (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a)
    (x y : WallComplement (fun j : D.active a => (D.wall j).support)) :
    (D.image e E hE).levelTransport k (hD.image (e := e) (E := E) (hE := hE) ha)
        ((D.levelPathImage e E hE k ha).obj x) ((D.levelPathImage e E hE k ha).obj y) =
      (E.gradedLieHom.truncatedMap k ha).bchGroupMap (D.levelTransport a hD x y) := by
  obtain ⟨p⟩ := D.exists_level_path a x y
  rw [(D.image e E hE).levelTransport_eq_levelPathProduct _
      ((D.levelPathImage e E hE k ha).mapPath p),
    D.levelPathProduct_image, D.levelTransport_eq_levelPathProduct hD p]

variable {D}

/-- Completed endpoint transport commutes with affine coordinate changes. -/
@[simp]
theorem transport_image (hD : D.Consistent) (x y : D.Point) :
    (D.image e E hE).transport (hD.image (e := e) (E := E) (hE := hE))
        ((D.pathImage e E hE).obj x) ((D.pathImage e E hE).obj y) =
      E.completedEquiv (D.transport hD x y) := by
  obtain ⟨p⟩ := D.exists_path x y
  rw [(D.image e E hE).transport_eq_pathProduct _ ((D.pathImage e E hE).mapPath p),
    D.pathProduct_image, D.transport_eq_pathProduct hD p]

end Mei.DirectedDiagram
