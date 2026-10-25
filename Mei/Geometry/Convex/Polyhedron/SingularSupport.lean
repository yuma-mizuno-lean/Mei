/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Boundary.Codimension

/-!
# Finite affine covers of polyhedral wall singularities

The singular support of a family is the union of its relative boundaries and
the intersections of members whose affine spans have different directions.
For a finite family of codimension-one polyhedra this actual set is covered by
finitely many affine subspaces of codimension at least two. Unbounded walls,
lineality and coincident or parallel supporting hyperplanes are allowed.
Continuous affine equivalences transport singular support, including under a
bijection of wall indices, by the intrinsic-frontier image theorem.
-/

public section

open Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Relative boundaries and intersections with different supporting directions
are the singular support of a wall family. -/
def singularSupport (W : ι → Set V) : Set V :=
  (⋃ i, intrinsicFrontier ℝ (W i)) ∪
    ⋃ i, ⋃ j ∈ {j | (affineSpan ℝ (W i)).direction ≠ (affineSpan ℝ (W j)).direction},
      W i ∩ W j

/-- Singular points lie on a relative boundary or on two members with
different affine supporting directions. -/
@[simp]
theorem mem_singularSupport {W : ι → Set V} {x : V} :
    x ∈ singularSupport W ↔ (∃ i, x ∈ intrinsicFrontier ℝ (W i)) ∨
      ∃ i j, (affineSpan ℝ (W i)).direction ≠ (affineSpan ℝ (W j)).direction ∧
        x ∈ W i ∧ x ∈ W j := by
  simp only [singularSupport, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_inter_iff, exists_prop]

/-- A point of a family member outside singular support lies in its relative interior. -/
theorem mem_intrinsicInterior_of_notMem_singularSupport {W : ι → Set V} {i : ι} {x : V}
    (hxi : x ∈ W i) (hx : x ∉ singularSupport W) :
    x ∈ intrinsicInterior ℝ (W i) := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  exact ⟨subset_intrinsicClosure hxi, fun hf => hx (mem_singularSupport.mpr (Or.inl ⟨i, hf⟩))⟩

/-- For closed wall carriers, singular support is contained in their union.
Thus points off all walls are automatically outside the actual singular support. -/
theorem singularSupport_subset_iUnion (W : ι → Set V) (hclosed : ∀ i, IsClosed (W i)) :
    singularSupport W ⊆ ⋃ i, W i := by
  intro x hx
  rcases mem_singularSupport.mp hx with ⟨i, hxi⟩ | ⟨i, j, _, hxi, _⟩
  · exact Set.mem_iUnion.mpr ⟨i, intrinsicFrontier_subset (hclosed i) hxi⟩
  · exact Set.mem_iUnion.mpr ⟨i, hxi⟩

/-- The singular support of finitely many codimension-one polyhedra has a
finite affine cover of codimension at least two. The cover is obtained from
their boundary covers and intersections of their supporting affine subspaces. -/
theorem exists_finite_singularSupport_cover [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V) :
    ∃ S : Finset (AffineSubspace ℝ V),
      singularSupport W ⊆ ⋃ A ∈ S, (A : Set V) ∧
      ∀ A ∈ S, Module.finrank ℝ A.direction + 1 < Module.finrank ℝ V := by
  classical
  let := Fintype.ofFinite ι
  choose S hcover hS using
    fun i => (hpoly i).exists_finite_intrinsicFrontier_cover_codim_two (hdim i)
  let B := Finset.univ.biUnion S
  let pairs := (Finset.univ : Finset (ι × ι)).filter (fun p =>
    (affineSpan ℝ (W p.1)).direction ≠ (affineSpan ℝ (W p.2)).direction)
  let T := pairs.image (fun p => affineSpan ℝ (W p.1) ⊓ affineSpan ℝ (W p.2))
  refine ⟨B ∪ T, ?_, ?_⟩
  · intro x hx
    rcases mem_singularSupport.mp hx with ⟨i, hxi⟩ | ⟨i, j, hne, hxi, hxj⟩
    · obtain ⟨A, hAi, hxA⟩ := Set.mem_iUnion₂.mp (hcover i hxi)
      apply Set.mem_iUnion₂.mpr
      refine ⟨A, Finset.mem_union_left _ ?_, hxA⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hAi⟩
    · apply Set.mem_iUnion₂.mpr
      refine ⟨affineSpan ℝ (W i) ⊓ affineSpan ℝ (W j), Finset.mem_union_right _ ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩
      · exact ⟨subset_affineSpan ℝ (W i) hxi, subset_affineSpan ℝ (W j) hxj⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, _, hAi⟩ := Finset.mem_biUnion.mp hA
      exact hS i A hAi
    · obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp hA
      have hne := (Finset.mem_filter.mp hp).2
      exact (affineSpan ℝ (W i)).finrank_direction_inf_add_one_lt
        (affineSpan ℝ (W j)) (hdim i) (hdim j) hne

end Mei.Convex

namespace ContinuousAffineEquiv

open Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {V' ι' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {W : ι → Set V} {W' : ι' → Set V'}

/-- Transporting and bijectively reindexing walls transports their singular support. -/
theorem singularSupport_image (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι')
    (hW : ∀ j, W' (r j) = e '' W j) : singularSupport W' = e '' singularSupport W := by
  have hd (j : ι) : (affineSpan ℝ (W' (r j))).direction =
      ((affineSpan ℝ (W j)).direction).map e.toAffineEquiv.linear.toLinearMap := by
    rw [hW]
    simpa only [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap,
      AffineEquiv.coe_coe, ContinuousAffineEquiv.coe_coe] using
      congrArg AffineSubspace.direction
        (AffineSubspace.map_span e.toAffineEquiv.toAffineMap (W j)).symm
  have hdir (j k : ι) :
      (affineSpan ℝ (W' (r j))).direction = (affineSpan ℝ (W' (r k))).direction ↔
        (affineSpan ℝ (W j)).direction = (affineSpan ℝ (W k)).direction := by
    rw [hd, hd]
    exact Submodule.map_injective_of_injective e.toAffineEquiv.linear.injective |>.eq_iff
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [e.injective.mem_set_image, mem_singularSupport, mem_singularSupport]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, k, hne, hj, hk⟩)
    · obtain ⟨j, rfl⟩ := r.surjective j
      rw [hW, e.intrinsicFrontier_image, e.injective.mem_set_image] at hj
      exact Or.inl ⟨j, hj⟩
    · obtain ⟨j, rfl⟩ := r.surjective j
      obtain ⟨k, rfl⟩ := r.surjective k
      exact Or.inr ⟨j, k, fun h => hne ((hdir j k).mpr h),
        (e.injective.mem_set_image).mp (hW j ▸ hj),
        (e.injective.mem_set_image).mp (hW k ▸ hk)⟩
  · rintro (⟨j, hj⟩ | ⟨j, k, hne, hj, hk⟩)
    · exact Or.inl ⟨r j, by rw [hW, e.intrinsicFrontier_image]; exact mem_image_of_mem e hj⟩
    · exact Or.inr ⟨r j, r k, fun h => hne ((hdir j k).mp h),
        by rw [hW]; exact mem_image_of_mem e hj,
        by rw [hW]; exact mem_image_of_mem e hk⟩

end ContinuousAffineEquiv
