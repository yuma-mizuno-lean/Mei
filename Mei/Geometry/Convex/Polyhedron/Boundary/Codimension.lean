/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Boundary
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Finite codimension bounds for polyhedral boundaries

The relative boundary of a polyhedron is covered by finitely many affine
subspaces of strictly smaller dimension. In particular, a wall of codimension
one has boundary contained in finitely many affine subspaces of codimension at
least two, as needed for generic path construction.
-/

public section

namespace AffineMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An affine zero section has strictly smaller affine span when the function
is nonzero somewhere on the original set. No convexity is needed. -/
theorem affineSpan_inter_zero_lt (g : V →ᵃ[ℝ] ℝ) {P : Set V}
    (hg : ∃ p ∈ P, g p ≠ 0) :
    affineSpan ℝ {x ∈ P | g x = 0} < affineSpan ℝ P := by
  refine lt_of_le_of_ne (affineSpan_mono ℝ (fun _ hx => hx.1)) ?_
  intro heq
  obtain ⟨p, hp, hgp⟩ := hg
  have hz : Set.EqOn g (0 : V →ᵃ[ℝ] ℝ) {x ∈ P | g x = 0} := fun _ hx => hx.2
  have hp' : p ∈ affineSpan ℝ {x ∈ P | g x = 0} := by
    rw [heq]
    exact subset_affineSpan ℝ P hp
  exact hgp (AffineMap.eqOn_affineSpan hz hp')

/-- A nonempty affine zero section has strictly smaller direction dimension
when the defining function is nonzero somewhere on the original set. -/
theorem finrank_direction_inter_zero_lt [FiniteDimensional ℝ V]
    (g : V →ᵃ[ℝ] ℝ) {P : Set V} (hne : {x ∈ P | g x = 0}.Nonempty)
    (hg : ∃ p ∈ P, g p ≠ 0) :
    Module.finrank ℝ (affineSpan ℝ {x ∈ P | g x = 0}).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction :=
  Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty (g.affineSpan_inter_zero_lt hg)
      (hne.affineSpan ℝ))

end AffineMap

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The relative boundary of a polyhedron is contained in finitely many affine
subspaces, each of strictly smaller direction dimension than the polyhedron.
Empty active faces are omitted, so the statement also handles empty sets. -/
theorem exists_finite_intrinsicFrontier_cover {P : Set V}
    (hP : TauCeti.IsConvexPolyhedron P) :
    ∃ S : Finset (AffineSubspace ℝ V),
      intrinsicFrontier ℝ P ⊆ ⋃ A ∈ S, (A : Set V) ∧
      ∀ A ∈ S, Module.finrank ℝ A.direction <
        Module.finrank ℝ (affineSpan ℝ P).direction := by
  classical
  obtain ⟨n, g, hP⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  let J := {j : Fin n | (∃ p ∈ P, g j p < 0) ∧ {x ∈ P | g j x = 0}.Nonempty}
  let S : Finset (AffineSubspace ℝ V) :=
    (Finset.univ.filter (fun j => j ∈ J)).image
      (fun j => affineSpan ℝ {x ∈ P | g j x = 0})
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    rw [Mei.Convex.intrinsicFrontier_eq_iUnion_active g hP] at hx
    obtain ⟨j, hj, hxP, hzero⟩ := Set.mem_iUnion₂.mp hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨affineSpan ℝ {x ∈ P | g j x = 0}, ?_, subset_affineSpan ℝ _ ⟨hxP, hzero⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj, ⟨x, hxP, hzero⟩⟩, rfl⟩
  · intro A hA
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨⟨p, hp, hgp⟩, hne⟩ := (Finset.mem_filter.mp hj).2
    exact (g j).toAffineMap.finrank_direction_inter_zero_lt hne ⟨p, hp, ne_of_lt hgp⟩

/-- The relative boundary of a codimension-one polyhedron is covered by
finitely many affine subspaces of codimension at least two. -/
theorem exists_finite_intrinsicFrontier_cover_codim_two {P : Set V}
    (hP : TauCeti.IsConvexPolyhedron P)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V) :
    ∃ S : Finset (AffineSubspace ℝ V),
      intrinsicFrontier ℝ P ⊆ ⋃ A ∈ S, (A : Set V) ∧
      ∀ A ∈ S, Module.finrank ℝ A.direction + 1 < Module.finrank ℝ V := by
  obtain ⟨S, hcover, hS⟩ := hP.exists_finite_intrinsicFrontier_cover
  refine ⟨S, hcover, fun A hA => ?_⟩
  rw [← hdim]
  exact Nat.add_lt_add_right (hS A hA) 1

end TauCeti.IsConvexPolyhedron
