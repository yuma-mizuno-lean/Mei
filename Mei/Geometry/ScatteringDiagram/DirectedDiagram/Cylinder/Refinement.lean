/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement

/-!
# Refinements through cylinder diagrams

A compatible refinement lifts to cylinders with exactly the same assignment of
nonidentity walls. Conversely, every refinement between cylinder diagrams descends
by taking a fixed-coordinate slice. These constructions are inverse: adjoining
unrestricted coordinates neither creates nor loses refinement data, including for
repeated indexed walls. Relative interiors commute with products, so the required
pairwise disjointness is preserved and reflected.

This completes the refinement comparison for the cylinder construction used in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2. We use Mathlib's
`intrinsicInterior_prod_eq` and the existing `DirectedDiagram.Refinement`.
-/

public section

noncomputable section

open Set

namespace Mei.DirectedDiagram

variable {Γ Λ K R L V E ι κ : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι}
  {F : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) κ}
  (h' : TauCeti.Toric.IsIntegralLattice j)

namespace Refinement

/-- Lift a refinement to cylinders, retaining its assignment of nonidentity walls. -/
def cylinder (r : D.Refinement F) : (D.cylinder h').Refinement (F.cylinder h') where
  assign a := r.assign ⟨a.val, by simpa using a.property⟩
  ray_eq a := by simpa using r.ray_eq ⟨a.val, by simpa using a.property⟩
  normal_eq a := by
    simp only [cylinder_wall, DirectedWall.cylinder_normal]
    rw [r.normal_eq ⟨a.val, by simpa using a.property⟩]
  label_eq a := by simpa using r.label_eq ⟨a.val, by simpa using a.property⟩
  support_subset a := by
    simp only [cylinder_wall, DirectedWall.cylinder_support]
    exact prod_mono_left (r.support_subset ⟨a.val, by simpa using a.property⟩)
  support_subset_iUnion a ha := by
    simp only [cylinder_wall, DirectedWall.cylinder_support, ← iUnion₂_prod_const]
    apply prod_mono_left
    simpa only [iUnion_subtype, cylinder_wall, DirectedWall.cylinder_label,
      mem_preimage, mem_singleton_iff] using
      r.support_subset_iUnion a (by simpa using ha)
  pairwiseDisjoint_intrinsicInterior a b hb c hc hbc := by
    simp only [cylinder_wall, DirectedWall.cylinder_support, intrinsicInterior_prod_eq]
    exact (r.pairwiseDisjoint_intrinsicInterior a hb hc
      (fun he => hbc (Subtype.ext (Subtype.mk.inj he)))).set_prod_left _ _

/-- Cylinder lifting leaves the wall assignment unchanged. -/
@[simp]
theorem cylinder_assign (r : D.Refinement F)
    (a : {a : κ // ((F.cylinder h').wall a).label ≠ 1}) :
    (r.cylinder h').assign a = r.assign ⟨a.val, by simpa using a.property⟩ := (rfl)

/-- Descend a refinement between cylinders to their base diagrams. -/
def ofCylinder (r : (D.cylinder h').Refinement (F.cylinder h')) : D.Refinement F where
  assign a := r.assign ⟨a.val, by simpa using a.property⟩
  ray_eq a := by simpa using r.ray_eq ⟨a.val, by simpa using a.property⟩
  normal_eq a := by
    have hn := r.normal_eq ⟨a.val, by simpa using a.property⟩
    simp only [cylinder_wall, DirectedWall.cylinder_normal] at hn
    ext x
    simpa using DFunLike.congr_fun hn (x, 0)
  label_eq a := by simpa using r.label_eq ⟨a.val, by simpa using a.property⟩
  support_subset a := by
    have hs := r.support_subset ⟨a.val, by simpa using a.property⟩
    simp only [cylinder_wall, DirectedWall.cylinder_support] at hs
    exact (prod_subset_prod_iff_left univ_nonempty).mp hs
  support_subset_iUnion a ha := by
    have hs := r.support_subset_iUnion a (by simpa using ha)
    simp only [cylinder_wall, DirectedWall.cylinder_support, ← iUnion₂_prod_const] at hs
    simpa only [iUnion_subtype, cylinder_wall, DirectedWall.cylinder_label,
      mem_preimage, mem_singleton_iff] using
      (prod_subset_prod_iff_left univ_nonempty).mp hs
  pairwiseDisjoint_intrinsicInterior a b hb c hc hbc := by
    have hd := r.pairwiseDisjoint_intrinsicInterior a hb hc
      (fun he => hbc (Subtype.ext (Subtype.mk.inj he)))
    simp only [cylinder_wall, DirectedWall.cylinder_support, intrinsicInterior_prod_eq] at hd
    have h0 : (0 : E) ∈ intrinsicInterior ℝ (univ : Set E) :=
      interior_subset_intrinsicInterior (by simp)
    exact (disjoint_prod.mp hd).resolve_right (not_disjoint_iff.mpr ⟨0, h0, h0⟩)

/-- Descending a cylinder refinement leaves its wall assignment unchanged. -/
@[simp]
theorem ofCylinder_assign (r : (D.cylinder h').Refinement (F.cylinder h'))
    (a : {a : κ // (F.wall a).label ≠ 1}) :
    (r.ofCylinder h').assign a = r.assign ⟨a.val, by simpa using a.property⟩ := (rfl)

/-- Descending the lift recovers the original refinement, including its assignment. -/
@[simp]
theorem ofCylinder_cylinder (r : D.Refinement F) : (r.cylinder h').ofCylinder h' = r := by
  ext a
  rfl

/-- Lifting the descended refinement recovers the original cylinder refinement. -/
@[simp]
theorem cylinder_ofCylinder (r : (D.cylinder h').Refinement (F.cylinder h')) :
    (r.ofCylinder h').cylinder h' = r := by
  ext a
  rfl

/-- Refinement data on base diagrams and on their cylinders are equivalent. -/
def cylinderEquiv : (D.Refinement F) ≃ ((D.cylinder h').Refinement (F.cylinder h')) where
  toFun := cylinder h'
  invFun := ofCylinder h'
  left_inv := ofCylinder_cylinder h'
  right_inv := cylinder_ofCylinder h'

/-- The cylinder equivalence computes by lifting a refinement. -/
@[simp]
theorem cylinderEquiv_apply (r : D.Refinement F) : cylinderEquiv h' r = r.cylinder h' := (rfl)

/-- Its inverse computes by descending a cylinder refinement. -/
@[simp]
theorem cylinderEquiv_symm_apply (r : (D.cylinder h').Refinement (F.cylinder h')) :
    (cylinderEquiv h').symm r = r.ofCylinder h' := (rfl)

end Refinement
end Mei.DirectedDiagram
