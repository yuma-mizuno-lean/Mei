/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Ray
public import Mei.Algebra.Lie.BCH.Ray.Basic
public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Geometry.Convex.Polyhedron.Rational
import Mei.Geometry.Convex.Polyhedron.Path.Completion

/-!
# Indexed walls and abelian-ray presentations of KS diagrams

An indexed wall of a KS space is a rational codimension-one cone in the hyperplane `w⊥` of a
supported ray `w`, labelled by an element of the completed group of that ray. An indexed wall
presentation is a family of indexed walls only finitely many of whose labels survive each
degree cutoff. Repeated supports keep distinct indices, and supports need not form a complex.

Two indexed walls with the same affine span lie on the same supported ray, since the degree
lattice is free. When rays are abelian (`IsAbelianRays`) their labels therefore commute, so at
each cutoff the active walls of a presentation have a finite path product: all signed labels
crossed at one time are multiplied without choosing an order. This is the abelian-ray
description of scattering diagrams in Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2), in the KS setting of Bridgeland, *Scattering
diagrams, Hall algebras and stability conditions*, §§2–3 (arXiv:1603.00416v4).

The path products use `Quiver.Path.wallPathProduct`; ray uniqueness is
`KSSpace.eq_of_mem_rayDegrees_of_ker_normal_le` and commutation is
`PositiveDegrees.commute_of_mem_completedRaySubgroup`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (s : KSSpace h) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A rational codimension-one cone in the hyperplane of a supported ray, labelled in the
completed group of that ray. Lineality is allowed. -/
@[ext]
structure IndexedWall where
  /-- The supported primitive ray indexing the wall. -/
  ray : SupportedRay d
  /-- The actual support, independent of an inequality presentation. -/
  support : Set V
  /-- The support is a cone with apex zero. -/
  isCone : ∃ σ : PointedCone ℝ V, (σ : Set V) = support
  /-- The support has rational normals. -/
  rational_support : IsRationalNormalPolyhedron h support
  /-- The support spans the hyperplane of the ray. -/
  direction_support :
    (affineSpan ℝ support).direction = LinearMap.ker (s.normal ray.generator)
  /-- The completed wall label. -/
  label : d.completedBCHGroup ℒ
  /-- The label lies in the completed group of the ray. -/
  label_mem : label ∈ d.completedRaySubgroup ℒ ray

namespace IndexedWall

variable {s d ℒ} (W : IndexedWall s d ℒ)

/-- The apex of the cone lies in the support. -/
@[simp]
theorem zero_mem_support : (0 : V) ∈ W.support := by
  obtain ⟨σ, hσ⟩ := W.isCone
  exact hσ ▸ σ.zero_mem

/-- The support is a closed convex polyhedron. -/
theorem isConvexPolyhedron : TauCeti.IsConvexPolyhedron W.support := by
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp W.rational_support
  rw [← hP]
  exact P.isConvexPolyhedron

/-- The normal of every degree on the ray cuts out the direction of the support. -/
theorem ker_normal_of_mem_rayDegrees {n : N} (hn : n ∈ W.ray.rayDegrees) :
    LinearMap.ker (s.normal n) = (affineSpan ℝ W.support).direction := by
  obtain ⟨a, ha, he⟩ := s.exists_normal_eq_smul_of_mem_rayDegrees hn
  rw [he, LinearMap.ker_smul _ _ ha.ne', W.direction_support]

/-- Every degree on the ray vanishes on the support. -/
theorem evaluation_eq_zero_of_mem_rayDegrees {n : N} (hn : n ∈ W.ray.rayDegrees) {θ : V}
    (hθ : θ ∈ W.support) : s.evaluation θ n = 0 := by
  have hmem : θ ∈ LinearMap.ker (s.normal n) := by
    rw [W.ker_normal_of_mem_rayDegrees hn, direction_affineSpan]
    simpa using vsub_mem_vectorSpan ℝ hθ W.zero_mem_support
  simpa using hmem

/-- The support has codimension one. -/
theorem finrank_direction_add_one :
    Module.finrank ℝ (affineSpan ℝ W.support).direction + 1 = Module.finrank ℝ V := by
  let := h.finiteDimensional
  obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
  rw [← W.ker_normal_of_mem_rayDegrees hn]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero
    (s.normal_ne_zero d (W.ray.rayDegrees_subset hn) (SupportedRay.ne_zero_of_mem_rayDegrees hn))

/-- Indexed walls with the same affine span lie on the same supported ray. -/
theorem ray_eq_of_affineSpan_eq [Module.Free ℤ N] (W W' : IndexedWall s d ℒ)
    (hWW' : affineSpan ℝ W.support = affineSpan ℝ W'.support) : W.ray = W'.ray := by
  obtain ⟨n, hn⟩ := W.ray.rayDegrees_nonempty
  obtain ⟨m, hm⟩ := W'.ray.rayDegrees_nonempty
  refine s.eq_of_mem_rayDegrees_of_ker_normal_le hn hm ?_
  rw [W.ker_normal_of_mem_rayDegrees hn, W'.ker_normal_of_mem_rayDegrees hm, hWW']

/-- With abelian rays, the labels of indexed walls with the same affine span commute. -/
theorem commute_label [Module.Free ℤ N] [IsAbelianRays d ℒ] (W W' : IndexedWall s d ℒ)
    (hWW' : affineSpan ℝ W.support = affineSpan ℝ W'.support) : Commute W.label W'.label :=
  d.commute_of_mem_completedRaySubgroup ℒ W.label_mem
    (W.ray_eq_of_affineSpan_eq W' hWW' ▸ W'.label_mem)

end IndexedWall

/-- A family of indexed walls with only finitely many labels surviving each degree cutoff.
Repeated walls retain distinct indices. -/
@[ext]
structure IndexedWallPresentation (ι : Type*) where
  /-- The indexed walls, with their supports and completed labels. -/
  wall : ι → IndexedWall s d ℒ
  /-- Only finitely many indexed labels are nonidentity at any fixed order. -/
  finite_active : CompletedGroup.HasFiniteSupport (fun j => (wall j).label)

namespace IndexedWallPresentation

variable {s d ℒ} {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)

/-- The indices whose labels survive the order-`k` projection. -/
def active (k : ℕ) : Set ι :=
  Function.mulSupport (fun j => CompletedGroup.projection k (D.wall j).label)

/-- Activity is exactly nontriviality of the projected label. -/
@[simp]
theorem mem_active (k : ℕ) (j : ι) :
    j ∈ D.active k ↔ CompletedGroup.projection k (D.wall j).label ≠ 1 := Iff.rfl

/-- The active wall index type is finite at every order. -/
instance finiteActive (k : ℕ) : Finite (D.active k) :=
  Set.finite_coe_iff.mpr (D.finite_active k)

/-- A label active at a lower order is also active at every higher order. -/
theorem active_mono : Monotone D.active :=
  CompletedGroup.monotone_mulSupport_projection (fun j => (D.wall j).label)

variable [Module.Free ℤ N] [IsAbelianRays d ℒ]

/-- The projected labels of active walls with the same affine span commute. -/
theorem activeLabels_commute (k : ℕ) (a b : D.active k)
    (hab : affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support) :
    Commute (CompletedGroup.projection k (D.wall a).label)
      (CompletedGroup.projection k (D.wall b).label) :=
  ((D.wall a).commute_label (D.wall b) hab).map (CompletedGroup.projection k)

/-- The order-`k` transport along a path admissible for the finite active wall family. Each
wall is cooriented by the normal of the generator of its ray. -/
def levelPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : d.truncatedGroup ℒ k :=
  p.wallPathProduct (fun j : D.active k => s.normal (D.wall j).ray.generator)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)

/-- The grouped wall-family product characterizes finite-order transport, independently
of which proof of coplanar commutation is used. -/
theorem levelPathProduct_eq_wallPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y)
    (comm : ∀ a b : D.active k,
      affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
        Commute (CompletedGroup.projection k (D.wall a).label)
          (CompletedGroup.projection k (D.wall b).label)) :
    D.levelPathProduct k p =
      p.wallPathProduct (fun j : D.active k => s.normal (D.wall j).ray.generator)
        (fun j => CompletedGroup.projection k (D.wall j).label) comm := (rfl)

@[simp]
theorem levelPathProduct_nil (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelPathProduct k (Quiver.Path.nil : AdmissiblePLPath x x) = 1 :=
  Quiver.Path.wallPathProduct_nil _ _ _

/-- Concatenated paths multiply with the second transport on the left. -/
@[simp]
theorem levelPathProduct_comp (k : ℕ)
    {x y z : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.levelPathProduct k (p.comp q) = D.levelPathProduct k q * D.levelPathProduct k p :=
  p.wallPathProduct_comp _ _ _ q

/-- Reversing a path inverts its finite-order transport. -/
@[simp]
theorem levelPathProduct_reverse (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p.reverse = (D.levelPathProduct k p)⁻¹ :=
  p.wallPathProduct_reverse _ _ _ (fun j : D.active k => (D.wall j).direction_support.symm)

/-- Lowering the cutoff projects transport and forgets exactly the walls that become inactive. -/
theorem truncation_levelPathProduct {k l : ℕ} (hkl : k ≤ l)
    {x y : WallComplement (fun j : D.active l => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.levelPathProduct l p) =
      D.levelPathProduct k
        ((WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
          (Set.inclusion (D.active_mono hkl))).mapPath p) := by
  have he := p.map_wallPathProduct_projection (fun j => (D.wall j).support)
    (fun j => s.normal (D.wall j).ray.generator) (fun j => (D.wall j).label)
    (fun a b hab => (D.wall a).commute_label (D.wall b) hab) D.active (fun _ => rfl) hkl
  simp only [PositiveDegrees.groupTower_map_hom] at he
  rw [D.levelPathProduct_eq_wallPathProduct l p (D.activeLabels_commute l),
    D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k)]
  exact he

end IndexedWallPresentation

end Mei
