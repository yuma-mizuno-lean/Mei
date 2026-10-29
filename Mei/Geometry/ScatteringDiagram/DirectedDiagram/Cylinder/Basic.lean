/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Cylinder
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic

/-!
# Cylinder lifts of directed diagrams

Lift projected directed walls to cylinders without changing indices, labels or
finite activity. Incomingness and outgoingness of each lifted wall are characterized
by `DirectedWall.cylinder_incoming_iff` and `DirectedWall.cylinder_outgoing_iff`.
The unrestricted coordinates may have arbitrary velocities; the construction uses
no injectivity of the projected degree map.

The construction applies `DirectedWall.cylinder` to the existing indexed wall
family, retaining the completed labels used in its finite-support condition.
Principal cylinders appear in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

variable {Γ Λ K R L V E ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι)
  (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Lift every wall to its cylinder, retaining the original index type. -/
def cylinder : DirectedDiagram (d := d) (h.prod h') H ι where
  wall a := (D.wall a).cylinder h'
  finite_active k := by simpa only [DirectedWall.cylinder_label] using D.finite_active k

@[simp]
theorem cylinder_wall (a : ι) : (D.cylinder h').wall a = (D.wall a).cylinder h' := (rfl)

/-- Cylinder lifting keeps exactly the same active indices at every cutoff. -/
@[simp]
theorem cylinder_active (k : ℕ) : (D.cylinder h').active k = D.active k := by
  ext a
  simp

variable (hfull : ∀ a, ∃ c : ℝ,
  (D.wall a).support = {x | h.realCharacter (D.wall a).normal x = c})

include hfull in
/-- A cylinder over a full affine hyperplane is again a full affine hyperplane,
with the pulled-back normal. -/
theorem cylinder_fullHyperplane : ∀ a, ∃ c : ℝ,
    ((D.cylinder h').wall a).support =
      {x | (h.prod h').realCharacter ((D.cylinder h').wall a).normal x = c} := by
  intro a
  obtain ⟨c, hc⟩ := hfull a
  refine ⟨c, ?_⟩
  rw [cylinder_wall, DirectedWall.cylinder_support,
    DirectedWall.realCharacter_cylinder_normal, hc]
  ext x
  simp

end Mei.DirectedDiagram
