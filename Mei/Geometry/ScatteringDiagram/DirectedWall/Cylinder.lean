/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Projection
public import Mei.Geometry.Affine.Span

/-!
# Cylinder lifts of directed walls

A wall for projected geometric directions lifts to a wall on the product space:
its support acquires an unrestricted second factor and its normal pulls back
along the first projection. The degree ray, completed label and cutoff orders
are retained. Incomingness and outgoingness are equivalent before and after
lifting, even when the projected degree direction vanishes.

This is the geometric cylinder construction used in the principal realization of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2. We use `DirectedWallSpaces.project` for labels,
`RationalAffinePolyhedron.preimage` for supports and
`TauCeti.Toric.IsIntegralLattice.realCharacter_comp` for normals.
-/

public section

noncomputable section

open Set

namespace Mei.DirectedWall

variable {Γ Λ K R L V E : Type*} [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (W : DirectedWall (d := d) h (H.project (AddMonoidHom.fst Λ K)))
  (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Lift a projected wall to the cylinder over its support, using the original
wall spaces on the product tangent lattice. -/
def cylinder : DirectedWall (d := d) (h.prod h') H where
  normal := W.normal.comp (AddMonoidHom.fst Λ K)
  normal_ne_zero := by
    intro hz
    apply W.normal_ne_zero
    ext a
    exact DFunLike.congr_fun hz (a, 0)
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support ×ˢ (univ : Set E)
  support_nonempty := W.support_nonempty.prod univ_nonempty
  rational_support := by
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp W.rational_support
    let f := (ContinuousLinearMap.fst ℝ V E).toContinuousAffineMap
    have hf : Toric.IsRationalLinearMap (h.prod h') h f.toAffineMap.linear :=
      Toric.IsRationalLinearMap.of_integral_compatible (h.prod h') h
        (AddMonoidHom.fst Λ K) f.toAffineMap.linear (fun _ => rfl)
    apply isRationalNormalPolyhedron_iff.mpr
    refine ⟨P.preimage f hf, (P.carrier_preimage f hf).trans ?_⟩
    rw [hP]
    ext x
    simp [f]
  direction_support := by
    rw [Mei.direction_affineSpan_prod_univ W.support_nonempty, W.direction_support,
      (h.prod h').realCharacter_comp h (AddMonoidHom.fst Λ K)
        (LinearMap.fst ℝ V E) (fun _ => rfl)]
    ext x
    simp
  label := W.label
  label_mem := (H.project_wallGroup (AddMonoidHom.fst Λ K) W.ray W.normal) ▸ W.label_mem

@[simp]
theorem cylinder_normal : (W.cylinder h').normal = W.normal.comp (AddMonoidHom.fst Λ K) :=
  (rfl)

@[simp]
theorem cylinder_ray : (W.cylinder h').ray = W.ray := (rfl)

@[simp]
theorem cylinder_support : (W.cylinder h').support = W.support ×ˢ (univ : Set E) := (rfl)

@[simp]
theorem cylinder_label : (W.cylinder h').label = W.label := (rfl)

/-- The real cylinder normal is the original real normal composed with projection. -/
theorem realCharacter_cylinder_normal :
    (h.prod h').realCharacter (W.cylinder h').normal =
      (h.realCharacter W.normal).comp (LinearMap.fst ℝ V E) := by
  rw [cylinder_normal]
  exact (h.prod h').realCharacter_comp h (AddMonoidHom.fst Λ K)
    (LinearMap.fst ℝ V E) (fun _ => rfl) W.normal

/-- Projection of the lifted spatial velocity is the original velocity. -/
@[simp]
theorem fst_cylinder_direction : (W.cylinder h').direction.1 = W.direction := by
  simp [direction_def]

/-- Cylinder lifting preserves and reflects incomingness, including zero
projected directions. The unrestricted coordinate creates no recession condition. -/
@[simp]
theorem cylinder_incoming_iff : (W.cylinder h').Incoming ↔ W.Incoming := by
  rw [incoming_iff, incoming_iff]
  constructor
  · intro hw x hx t ht
    exact (hw (x, 0) ⟨hx, mem_univ _⟩ t ht).1
  · intro hw x hx t ht
    exact ⟨hw x.1 hx.1 t ht, mem_univ _⟩

/-- Cylinder lifting also preserves and reflects outgoingness. -/
@[simp]
theorem cylinder_outgoing_iff : (W.cylinder h').Outgoing ↔ W.Outgoing := by
  rw [outgoing_iff, outgoing_iff]
  rw [mem_recessionCone, mem_recessionCone, ← incoming_iff, ← incoming_iff]
  exact not_congr (W.cylinder_incoming_iff h')

end Mei.DirectedWall
