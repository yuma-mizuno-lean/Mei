/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Completion

/-!
# Consistent directed diagrams and endpoint transport

Finite-order consistency means that active-wall products depend only on endpoints.
It is equivalent to triviality of admissible loop products. Consistency supplies
endpoint transport at each cutoff, compatible with lowering the cutoff. These
finite transports are the chamber transports used when lifting a lower-order
trivialization to the next order.

For a diagram consistent at every cutoff, transport between all-order allowed
points takes values in the completed BCH group. Its projection can be computed
using any path admissible at that cutoff, without choosing a common path for the
computation. Concatenation puts the later transport on the left.

This follows the endpoint-transport construction for `Mei.CompletedDiagram` and
uses `DirectedDiagram.truncation_levelPathProduct`, the finite-family path
existence theorem `AdmissiblePLPath.exists_length_eq_two`, and the all-order
path existence theorem `DirectedDiagram.exists_path`. The same construction
applies to repeated and overlapping indexed walls with grouped coplanar crossings.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Consistency at order `k` is endpoint independence of active-wall products. -/
def LevelConsistent (k : ℕ) : Prop :=
  ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
    (p q : AdmissiblePLPath x y), D.levelPathProduct k p = D.levelPathProduct k q

/-- The endpoint characterization of finite-order consistency. -/
theorem levelConsistent_def (k : ℕ) : D.LevelConsistent k ↔
    ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
      (p q : AdmissiblePLPath x y), D.levelPathProduct k p = D.levelPathProduct k q := Iff.rfl

/-- Finite-order consistency is equivalent to triviality of every admissible loop. -/
theorem levelConsistent_iff_loops (k : ℕ) : D.LevelConsistent k ↔
    ∀ (x : WallComplement (fun j : D.active k => (D.wall j).support))
      (p : AdmissiblePLPath x x), D.levelPathProduct k p = 1 := by
  constructor
  · intro hc x p
    simpa using hc p .nil
  · intro hc x y p q
    have he := hc x (p.comp q.reverse)
    exact (inv_mul_eq_one.mp (by
      simpa only [levelPathProduct_comp, levelPathProduct_reverse] using he)).symm

/-- Any endpoints allowed at a fixed cutoff admit a finite-order admissible path. -/
theorem exists_level_path (k : ℕ)
    (x y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    Nonempty (AdmissiblePLPath x y) := by
  let := h.finiteDimensional
  obtain ⟨p, _⟩ := AdmissiblePLPath.exists_length_eq_two
    (fun j : D.active k => (D.wall j).isConvexPolyhedron)
    (fun j => (D.wall j).finrank_direction_add_one) x y
  exact ⟨p⟩

/-- Endpoint transport at a consistent finite order. -/
def levelTransport (k : ℕ) (_hD : D.LevelConsistent k)
    (x y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    d.truncatedGroup ℒ k :=
  D.levelPathProduct k (D.exists_level_path k x y).some

/-- Finite-order transport is computed by any admissible path with the given endpoints. -/
theorem levelTransport_eq_levelPathProduct {k : ℕ} (hD : D.LevelConsistent k)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelTransport k hD x y = D.levelPathProduct k p := by
  rw [levelTransport]
  exact hD _ p

@[simp]
theorem levelTransport_self {k : ℕ} (hD : D.LevelConsistent k)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelTransport k hD x x = 1 := by
  rw [D.levelTransport_eq_levelPathProduct hD Quiver.Path.nil, levelPathProduct_nil]

/-- Finite-order endpoint transports compose in traversal order. -/
theorem levelTransport_comp {k : ℕ} (hD : D.LevelConsistent k)
    (x y z : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelTransport k hD x z = D.levelTransport k hD y z * D.levelTransport k hD x y := by
  obtain ⟨p⟩ := D.exists_level_path k x y
  obtain ⟨q⟩ := D.exists_level_path k y z
  rw [D.levelTransport_eq_levelPathProduct hD (p.comp q), levelPathProduct_comp,
    D.levelTransport_eq_levelPathProduct hD p, D.levelTransport_eq_levelPathProduct hD q]

/-- Interchanging finite-order endpoints inverts transport. -/
theorem levelTransport_swap {k : ℕ} (hD : D.LevelConsistent k)
    (x y : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelTransport k hD y x = (D.levelTransport k hD x y)⁻¹ := by
  obtain ⟨p⟩ := D.exists_level_path k x y
  rw [D.levelTransport_eq_levelPathProduct hD p.reverse, levelPathProduct_reverse,
    D.levelTransport_eq_levelPathProduct hD p]

/-- Lowering the cutoff projects endpoint transport, independently of path choices. -/
theorem truncation_levelTransport {k l : ℕ} (hkl : k ≤ l)
    (hk : D.LevelConsistent k) (hl : D.LevelConsistent l)
    (x y : WallComplement (fun j : D.active l => (D.wall j).support)) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.levelTransport l hl x y) =
      D.levelTransport k hk
        ((WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
          (Set.inclusion (D.active_mono hkl))).obj x)
        ((WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
          (Set.inclusion (D.active_mono hkl))).obj y) := by
  obtain ⟨p⟩ := D.exists_level_path l x y
  rw [D.levelTransport_eq_levelPathProduct hl p, D.truncation_levelPathProduct hkl p,
    D.levelTransport_eq_levelPathProduct hk]

/-- A directed diagram is consistent when it is consistent at every finite cutoff. -/
def Consistent : Prop := ∀ k, D.LevelConsistent k

/-- Consistency is exactly finite-order endpoint independence at every cutoff. -/
theorem consistent_iff : D.Consistent ↔ ∀ k, D.LevelConsistent k := Iff.rfl

/-- A diagram is consistent exactly when all its finite-order loop products vanish. -/
theorem consistent_iff_loops : D.Consistent ↔
    ∀ (k : ℕ) (x : WallComplement (fun j : D.active k => (D.wall j).support))
      (p : AdmissiblePLPath x x), D.levelPathProduct k p = 1 := by
  simp only [consistent_iff, levelConsistent_iff_loops]

variable {D} {x y z : D.Point}

/-- Finite-order consistency makes completed products independent of the all-order path. -/
theorem Consistent.pathProduct_eq (hD : D.Consistent) (p q : Quiver.Path x y) :
    D.pathProduct p = D.pathProduct q := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_pathProduct]
  exact hD k _ _

variable (D)

/-- Completed endpoint transport in a consistent directed diagram. -/
def transport (_hD : D.Consistent) (x y : D.Point) : d.completedBCHGroup ℒ :=
  D.pathProduct (D.exists_path x y).some

/-- Completed transport is computed by any common all-order admissible path. -/
theorem transport_eq_pathProduct (hD : D.Consistent) (p : Quiver.Path x y) :
    D.transport hD x y = D.pathProduct p := by
  rw [transport]
  exact hD.pathProduct_eq _ p

/-- Any finite-order path computes the corresponding projection of completed transport. -/
theorem projection_transport (hD : D.Consistent) (k : ℕ)
    (p : AdmissiblePLPath (CommonWallComplement.projection k x)
      (CommonWallComplement.projection k y)) :
    CompletedGroup.projection k (D.transport hD x y) = D.levelPathProduct k p := by
  rw [transport, projection_pathProduct]
  exact hD k _ p

/-- Completed endpoint transport projects to the finite-order endpoint transport. -/
@[simp]
theorem projection_transport_eq_levelTransport (hD : D.Consistent) (k : ℕ) :
    CompletedGroup.projection k (D.transport hD x y) =
      D.levelTransport k ((D.consistent_iff.mp hD) k) (CommonWallComplement.projection k x)
        (CommonWallComplement.projection k y) := by
  obtain ⟨p⟩ := D.exists_level_path k
    (CommonWallComplement.projection k x) (CommonWallComplement.projection k y)
  rw [D.projection_transport hD k p, D.levelTransport_eq_levelPathProduct (hD k) p]

@[simp]
theorem transport_self (hD : D.Consistent) (x : D.Point) : D.transport hD x x = 1 := by
  rw [D.transport_eq_pathProduct hD Quiver.Path.nil, pathProduct_nil]

/-- Completed transports compose with the later transport on the left. -/
theorem transport_comp (hD : D.Consistent) (x y z : D.Point) :
    D.transport hD x z = D.transport hD y z * D.transport hD x y := by
  obtain ⟨p⟩ := D.exists_path x y
  obtain ⟨q⟩ := D.exists_path y z
  rw [D.transport_eq_pathProduct hD (p.comp q), pathProduct_comp,
    D.transport_eq_pathProduct hD p, D.transport_eq_pathProduct hD q]

/-- Interchanging all-order endpoints inverts completed transport. -/
theorem transport_swap (hD : D.Consistent) (x y : D.Point) :
    D.transport hD y x = (D.transport hD x y)⁻¹ := by
  obtain ⟨p⟩ := D.exists_path x y
  rw [D.transport_eq_pathProduct hD p.reverse, pathProduct_reverse,
    D.transport_eq_pathProduct hD p]

end Mei.DirectedDiagram
