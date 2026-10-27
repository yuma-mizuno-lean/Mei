/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness

/-!
# Consistency and outgoing completions under coordinate changes

Integral affine changes of spatial coordinates and compatible changes of the
graded Lie data preserve and reflect consistency. The positive degree functions
may differ: consistency at a source cutoff controls every target cutoff covered
by its modulus. Consequently actual outgoing completions transport to outgoing
completions, and their completed endpoint transports commute with coordinates.

Finite-order comparisons apply to every target-admissible loop, even when
source-active labels disappear at the target cutoff. Repeated indexed walls,
translations and orientation-reversing spatial equivalences are allowed.
-/

/- The proof combines `DirectedDiagram.levelPathProduct_image` with the
moving-basepoint perturbation in `DirectedDiagram.LevelEquivalent.consistent`. -/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι ι₀ ι' : Type*} {L L' : Type u}
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

/-- Consistency at a source cutoff implies consistency at every target cutoff
covered by the coordinate change's modulus. No common-path condition is imposed
on target loops. -/
theorem levelConsistent_image (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a) : (D.image e E hE).LevelConsistent k := by
  have := h'.finiteDimensional
  apply ((D.image e E hE).levelConsistent_iff_loops k).mpr
  intro x p
  cases p with
  | nil => simp
  | @cons y _ p f =>
    let loop := p.cons f
    obtain ⟨ε, hε, hp⟩ := (D.image e E hE).exists_pos_levelPathProduct_eq_of_forall₂_dist_lt
      k loop
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
    have hv : loop.vertices.map WallComplement.val =
        x.val :: (l.map WallComplement.val ++ [x.val]) := by
      simp only [loop, Quiver.Path.vertices_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, hl, List.cons_append]
    let W : D.active a → Set V' := fun j => ((D.wall j).image e E hE).support
    have hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j) :=
      fun j => ((D.wall j).image e E hE).isConvexPolyhedron
    have hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
        Module.finrank ℝ V' := fun j => ((D.wall j).image e E hE).finrank_direction_add_one
    obtain ⟨z, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hpoly hdim x.val
      (l := l.map WallComplement.val) hε
    -- Pull the perturbed loop back through all source-active supports.
    let B := e.symm.toContinuousAffineEquiv.wallComplementMap (Equiv.refl (D.active a))
      (W := W) (W' := fun j : D.active a => (D.wall j).support) (by
        intro j
        simp only [Equiv.refl_apply, W, DirectedWall.image_support]
        ext v
        simp)
    let r := B.mapPath q
    let s := (D.levelPathImage e E hE k ha).mapPath r
    have hs : s.vertices.map WallComplement.val = q.vertices.map WallComplement.val := by
      simp only [s, r, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        levelPathImage_obj_val]
      apply List.map_congr_left
      intro v _
      simp [B, Toric.IntegralAffineEquiv.symm_toAffineEquiv]
    have hprod : (D.image e E hE).levelPathProduct k s = 1 := by
      rw [D.levelPathProduct_image e E hE k ha r,
        ((D.levelConsistent_iff_loops a).mp hD _ r), map_one]
    exact (hp s (by simpa only [hv, hs] using hq)).symm.trans hprod

/-- Finite endpoint transport is natural at any source cutoff covering the
coordinate modulus. The target endpoints need only be images of the given
source endpoints. -/
theorem levelTransport_image (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a)
    (x y : WallComplement (fun j : D.active a => (D.wall j).support)) :
    (D.image e E hE).levelTransport k (D.levelConsistent_image e E hE k ha hD)
        ((D.levelPathImage e E hE k ha).obj x) ((D.levelPathImage e E hE k ha).obj y) =
      (E.gradedLieHom.truncatedMap k ha).bchGroupMap (D.levelTransport a hD x y) := by
  obtain ⟨p⟩ := D.exists_level_path a x y
  rw [(D.image e E hE).levelTransport_eq_levelPathProduct _
      ((D.levelPathImage e E hE k ha).mapPath p),
    D.levelPathProduct_image, D.levelTransport_eq_levelPathProduct hD p]

variable {D}

/-- Coordinate changes preserve consistency even when the cutoff functions differ. -/
theorem Consistent.image (hD : D.Consistent) : (D.image e E hE).Consistent := by
  apply ((D.image e E hE).consistent_iff).mpr
  intro k
  exact D.levelConsistent_image e E hE k le_rfl
    ((D.consistent_iff.mp hD) (E.degreeMap.modulus k))

/-- Consistency is invariant under compatible spatial and algebraic coordinates. -/
@[simp]
theorem consistent_image_iff : (D.image e E hE).Consistent ↔ D.Consistent := by
  constructor
  · intro hD
    have he := hD.image e.symm E.symm (by simp [hE])
    simpa only [image_symm_image] using he
  · exact fun hD => hD.image e E hE

/-- Completed endpoint transport commutes with affine coordinate changes. -/
theorem transport_image (hD : D.Consistent) (x y : D.Point) :
    (D.image e E hE).transport (hD.image e E hE)
        ((D.pathImage e E hE).obj x) ((D.pathImage e E hE).obj y) =
      E.completedEquiv (D.transport hD x y) := by
  obtain ⟨p⟩ := D.exists_path x y
  rw [(D.image e E hE).transport_eq_pathProduct _ ((D.pathImage e E hE).mapPath p),
    D.pathProduct_image, D.transport_eq_pathProduct hD p]

/-- An affine coordinate change transports every actual outgoing completion,
including its specified initial walls. -/
theorem IsOutgoingCompletion.image
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hD : IsOutgoingCompletion D₀ D) :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) where
  wall_inl j := by simp only [image_wall, hD.wall_inl]
  outgoing_inr j := by
    rw [image_wall, DirectedWall.outgoing_image_iff]
    exact hD.outgoing_inr j
  consistent := hD.consistent.image e E hE

/-- Affine coordinate changes also reflect the outgoing-completion property. -/
@[simp]
theorem isOutgoingCompletion_image_iff
    {D₀ : ι₀ → DirectedWall (d := d) h H}
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) ↔
      IsOutgoingCompletion D₀ D := by
  constructor
  · intro hD
    have he := hD.image e.symm E.symm (by simp [hE])
    simpa only [image_symm_image, DirectedWall.image_symm_image] using he
  · exact fun hD => hD.image e E hE

end Mei.DirectedDiagram
