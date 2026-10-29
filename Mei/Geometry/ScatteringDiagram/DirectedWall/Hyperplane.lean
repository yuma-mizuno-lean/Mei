/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.Polyhedron.SignCell.Rational

/-!
# Walls supported on linear hyperplanes

A nonzero integral normal, a tangent supported ray and a label in its wall group
determine an incoming wall on the entire kernel of the real normal. These walls
provide full-hyperplane inputs, in particular the coefficient probe wall.

We use `Convex.isRationalNormalPolyhedron_weakSignCell` for the support and
Mathlib's `Submodule.toAffineSubspace` for its affine direction.
-/

public section
noncomputable section

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (H : DirectedWallSpaces ρ ℒ)

/-- The full linear hyperplane with a specified tangent ray and wall-group label. -/
def ofLinearHyperplane (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) : DirectedWall (d := d) h H where
  normal := m
  normal_ne_zero := hm
  ray := w
  normal_direction := hw
  support := (h.realCharacter m).ker
  support_nonempty := ⟨0, by simp⟩
  rational_support := by
    let := h.finiteDimensional
    let f := (h.realCharacter m).toContinuousLinearMap.toContinuousAffineMap
    have hf := Convex.isRationalNormalPolyhedron_weakSignCell (fun _ : Unit => f)
      (fun _ => Toric.IsRationalFunctional.realCharacter h m.toIntLinearMap) (fun _ => 0)
    have he : Convex.weakSignCell (fun _ : Unit => f) (fun _ => 0) =
        ((h.realCharacter m).ker : Set V) := by
      ext x
      simp [f]
    rwa [he] at hf
  direction_support := by
    -- The affine hull API takes an affine subspace, so view the kernel as one.
    exact (congrArg AffineSubspace.direction
      (AffineSubspace.affineSpan_coe (h.realCharacter m).ker.toAffineSubspace)).trans
        (Submodule.toAffineSubspace_direction _)
  label := g
  label_mem := g.property

@[simp]
theorem ofLinearHyperplane_normal (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofLinearHyperplane h H m hm w hw g).normal = m := (rfl)

@[simp]
theorem ofLinearHyperplane_ray (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofLinearHyperplane h H m hm w hw g).ray = w := (rfl)

@[simp]
theorem ofLinearHyperplane_support (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofLinearHyperplane h H m hm w hw g).support = (h.realCharacter m).ker := (rfl)

@[simp]
theorem ofLinearHyperplane_label (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofLinearHyperplane h H m hm w hw g).label = g := (rfl)

/-- Full linear hyperplanes are incoming, including zero spatial directions. -/
@[simp]
theorem ofLinearHyperplane_incoming (m : Λ →+ ℤ) (hm : m ≠ 0) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofLinearHyperplane h H m hm w hw g).Incoming := by
  rw [incoming_iff]
  intro x hx t ht
  simp only [ofLinearHyperplane_support, SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
  simp [hx, hw]

end Mei.DirectedWall
