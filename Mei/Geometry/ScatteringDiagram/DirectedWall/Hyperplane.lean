/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.Polyhedron.SignCell.Rational

/-!
# Walls supported on full hyperplanes

A nonzero integral normal `m`, a real offset `c`, a tangent supported ray and a label in its
wall group determine an incoming wall on the entire affine hyperplane `{x | ℓ x = c}`, where
`ℓ` is the real extension of `m` (`DirectedWall.ofAffineHyperplane`). The offset zero gives the
walls on the kernel of the real normal. These walls provide full-hyperplane inputs, in particular
the coefficient probe wall and the cylinders over the affine incoming lines of rank-two
polynomial inputs. Every level set of `ℓ` is nonempty, since `ℓ` is nonzero
(`TauCeti.Toric.IsIntegralLattice.exists_realCharacter_eq`).

We use `isRationalNormalPolyhedron_setOf_le` for the support and Mathlib's
`AffineSubspace.mk'` for its affine direction.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

open TauCeti (DirectedWallSpaces)
noncomputable section

namespace TauCeti.Toric.IsIntegralLattice

variable {Λ V : Type*} [AddCommGroup Λ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : IsIntegralLattice i)

/-- The real extension of a nonzero integral functional is nonzero at some point. -/
theorem exists_realCharacter_ne_zero {m : Λ →+ ℤ} (hm : m ≠ 0) :
    ∃ x, h.realCharacter m x ≠ 0 := by
  by_contra! hx
  exact hm (h.realCharacter_injective (by rw [map_zero]; exact LinearMap.ext hx))

/-- Every level set `{ℓ = c}` of the real extension `ℓ` of a nonzero integral functional is
nonempty. -/
theorem exists_realCharacter_eq {m : Λ →+ ℤ} (hm : m ≠ 0) (c : ℝ) :
    ∃ x, h.realCharacter m x = c := by
  obtain ⟨x, hx⟩ := h.exists_realCharacter_ne_zero hm
  exact ⟨(c / h.realCharacter m x) • x, by simp [hx]⟩

end TauCeti.Toric.IsIntegralLattice

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (H : DirectedWallSpaces ρ ℒ)

/-- The full affine hyperplane `{x | ℓ x = c}`, `ℓ` the real extension of the integral normal,
with a specified tangent ray and wall-group label. The offset `c` is an arbitrary real number. -/
def ofAffineHyperplane (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) : DirectedWall (d := d) h H where
  normal := m
  normal_ne_zero := hm
  ray := w
  normal_direction := hw
  support := {x | h.realCharacter m x = c}
  support_nonempty := h.exists_realCharacter_eq hm c
  rational_support := by
    let := h.finiteDimensional
    let ℓ := (h.realCharacter m).toContinuousLinearMap
    have hℓ : Toric.IsRationalFunctional h ℓ.toLinearMap :=
      Toric.IsRationalFunctional.realCharacter h m.toIntLinearMap
    have he : {x | h.realCharacter m x = c} = {x | ℓ x ≤ c} ∩ {x | (-ℓ) x ≤ -c} := by
      ext x
      simp [ℓ, le_antisymm_iff]
    rw [he]
    exact (isRationalNormalPolyhedron_setOf_le ℓ hℓ c).inter
      (isRationalNormalPolyhedron_setOf_le (-ℓ) (by simpa using hℓ.neg) (-c))
  direction_support := by
    obtain ⟨p, hp⟩ := h.exists_realCharacter_eq hm c
    have he : {x | h.realCharacter m x = c} =
        (AffineSubspace.mk' p (LinearMap.ker (h.realCharacter m)) : Set V) := by
      ext y
      simp [AffineSubspace.mem_mk', hp, sub_eq_zero]
    rw [he, AffineSubspace.affineSpan_coe, AffineSubspace.direction_mk']
  label := g
  label_mem := g.property

/-- The normal of an affine hyperplane wall is the given integral normal. -/
@[simp]
theorem ofAffineHyperplane_normal (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofAffineHyperplane h H m hm c w hw g).normal = m := (rfl)

/-- The ray of an affine hyperplane wall is the given supported ray. -/
@[simp]
theorem ofAffineHyperplane_ray (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofAffineHyperplane h H m hm c w hw g).ray = w := (rfl)

/-- The support of an affine hyperplane wall is the level set `{ℓ = c}`. -/
@[simp]
theorem ofAffineHyperplane_support (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofAffineHyperplane h H m hm c w hw g).support = {x | h.realCharacter m x = c} := (rfl)

/-- The label of an affine hyperplane wall is the given wall-group label. -/
@[simp]
theorem ofAffineHyperplane_label (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofAffineHyperplane h H m hm c w hw g).label = g := (rfl)

/-- Full affine hyperplanes are incoming: their support is preserved by every tangent
translation, including zero spatial directions. -/
@[simp]
theorem ofAffineHyperplane_incoming (m : Λ →+ ℤ) (hm : m ≠ 0) (c : ℝ) (w : SupportedRay d)
    (hw : m (ρ w.generator) = 0) (g : H.wallGroup w m) :
    (ofAffineHyperplane h H m hm c w hw g).Incoming := by
  rw [incoming_iff]
  intro x hx t _
  simp only [ofAffineHyperplane_support, Set.mem_ofPred_eq] at hx ⊢
  simp [hx, hw]

end Mei.DirectedWall
