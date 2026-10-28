/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Boundary.Codimension
public import Mei.Geometry.Affine.Span
import Mei.Analysis.Convex.Intrinsic

/-!
# Finite affine covers of polyhedral wall singularities

The singular support of a family is the union of its relative boundaries and
the intersections of members whose affine spans have different directions.
For a finite family of codimension-one polyhedra this actual set is covered by
finitely many affine subspaces of codimension at least two. Unbounded walls,
lineality and coincident or parallel supporting hyperplanes are allowed.
Continuous affine equivalences transport singular support, including under a
bijection of wall indices, by the intrinsic-frontier image theorem. Finitely
many closed walls in finite dimension have closed singular support.
Covering each closed wall by pieces with the same affine span can only enlarge
singular support; extra fine walls are allowed. Adding unrestricted coordinates
to every wall gives the cylinder over the original singular support, including
for families with empty walls. On a convex set avoiding singular support, each wall
meeting the set agrees there with its affine span, and distinct wall directions cannot cross.
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

/-- The singular support of finitely many closed walls is closed in finite
dimension. No polyhedral or codimension hypothesis is needed. -/
theorem isClosed_singularSupport [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hclosed : ∀ i, IsClosed (W i)) :
    IsClosed (singularSupport W) := by
  unfold singularSupport
  exact (isClosed_iUnion_of_finite fun i =>
    isClosed_intrinsicFrontier (affineSpan ℝ (W i)).closed_of_finiteDimensional).union
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => (hclosed i).inter (hclosed j))

/-- Restricting or reindexing a wall family introduces no new singular points. -/
theorem singularSupport_comp_subset {κ : Type*} (W : ι → Set V) (f : κ → ι) :
    singularSupport (W ∘ f) ⊆ singularSupport W := by
  intro x hx
  rcases mem_singularSupport.mp hx with ⟨j, hj⟩ | ⟨j, k, hne, hj, hk⟩
  · exact mem_singularSupport.mpr (Or.inl ⟨f j, hj⟩)
  · exact mem_singularSupport.mpr (Or.inr ⟨f j, f k, hne, hj, hk⟩)

/-- A point of a family member outside singular support lies in its relative interior. -/
theorem mem_intrinsicInterior_of_notMem_singularSupport {W : ι → Set V} {i : ι} {x : V}
    (hxi : x ∈ W i) (hx : x ∉ singularSupport W) :
    x ∈ intrinsicInterior ℝ (W i) := by
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  exact ⟨subset_intrinsicClosure hxi, fun hf => hx (mem_singularSupport.mpr (Or.inl ⟨i, hf⟩))⟩

/-- Covering closed walls by pieces with the same affine span introduces no
new singular points in the coarse family. The fine family may have extra walls. -/
theorem singularSupport_subset_of_wall_cover {κ : Type*} {W : ι → Set V} {W' : κ → Set V}
    (hclosed : ∀ j, IsClosed (W j))
    (hcover : ∀ j x, x ∈ W j → ∃ a, x ∈ W' a ∧ W' a ⊆ W j ∧
      affineSpan ℝ (W' a) = affineSpan ℝ (W j)) :
    singularSupport W ⊆ singularSupport W' := by
  intro x hx
  by_contra hregular
  rcases mem_singularSupport.mp hx with ⟨j, hxj⟩ | ⟨j, l, hne, hxj, hxl⟩
  · obtain ⟨a, hxa, hsub, hspan⟩ := hcover j x (intrinsicFrontier_subset (hclosed j) hxj)
    have hint := mem_intrinsicInterior_of_notMem_singularSupport hxa hregular
    have hi : x ∈ intrinsicInterior ℝ (W j) := by
      rw [intrinsicInterior, hspan] at hint
      exact image_mono (interior_mono (preimage_mono hsub)) hint
    exact (intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ) (W j) ▸ hxj).2 hi
  · obtain ⟨a, hxa, -, hspan⟩ := hcover j x hxj
    obtain ⟨b, hxb, -, hspan'⟩ := hcover l x hxl
    apply hregular
    exact mem_singularSupport.mpr (Or.inr ⟨a, b, by rwa [hspan, hspan'], hxa, hxb⟩)

/-- For closed wall carriers, singular support is contained in their union.
Thus points off all walls are automatically outside the actual singular support. -/
theorem singularSupport_subset_iUnion (W : ι → Set V) (hclosed : ∀ i, IsClosed (W i)) :
    singularSupport W ⊆ ⋃ i, W i := by
  intro x hx
  rcases mem_singularSupport.mp hx with ⟨i, hxi⟩ | ⟨i, j, _, hxi, _⟩
  · exact Set.mem_iUnion.mpr ⟨i, intrinsicFrontier_subset (hclosed i) hxi⟩
  · exact Set.mem_iUnion.mpr ⟨i, hxi⟩

/-- A continuous affine change of coordinates transports the actual singular support,
including relative boundaries and intersections of different wall directions. -/
@[simp]
theorem singularSupport_image {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (W : ι → Set V) (e : V ≃ᴬ[ℝ] U) :
    singularSupport (fun i => e '' W i) = e '' singularSupport W := by
  -- The span transport API uses the affine-map coercion, rather than the equivalence coercion.
  have hcoe : (e.toAffineEquiv.toAffineMap : V → U) = e := by rfl
  have hdir (i j : ι) :
      (affineSpan ℝ (e '' W i)).direction = (affineSpan ℝ (e '' W j)).direction ↔
        (affineSpan ℝ (W i)).direction = (affineSpan ℝ (W j)).direction := by
    rw [← hcoe, ← AffineSubspace.map_span e.toAffineEquiv.toAffineMap,
      ← AffineSubspace.map_span e.toAffineEquiv.toAffineMap,
      AffineSubspace.map_direction, AffineSubspace.map_direction]
    exact (Submodule.map_injective_of_injective e.toAffineEquiv.linear.injective).eq_iff
  ext u
  obtain ⟨x, rfl⟩ := e.surjective u
  simp only [mem_singularSupport, e.intrinsicFrontier_image, e.injective.mem_set_image,
    ne_eq, hdir]

/-- A cylinder family has precisely the singularities of the original family.
Empty members are allowed. -/
@[simp]
theorem singularSupport_prod_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : ι → Set V) :
    singularSupport (fun j => W j ×ˢ (univ : Set E)) = singularSupport W ×ˢ univ := by
  ext x
  simp only [mem_singularSupport, Mei.intrinsicFrontier_prod_univ, mem_prod, mem_univ,
    and_true]
  constructor
  · rintro (hfront | ⟨i, j, hne, hi, hj⟩)
    · exact Or.inl hfront
    · exact Or.inr ⟨i, j, fun he => hne
        ((Mei.direction_affineSpan_prod_univ_eq_iff
          ⟨x.1, hi⟩ ⟨x.1, hj⟩).mpr he), hi, hj⟩
  · rintro (hfront | ⟨i, j, hne, hi, hj⟩)
    · exact Or.inl hfront
    · exact Or.inr ⟨i, j, fun he => hne
        ((Mei.direction_affineSpan_prod_univ_eq_iff
          ⟨x.1, hi⟩ ⟨x.1, hj⟩).mp he), hi, hj⟩

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
    simpa only [AffineEquiv.linear_toAffineMap,
      AffineEquiv.coe_coe, ContinuousAffineEquiv.coe_coe] using
      e.toAffineEquiv.toAffineMap.direction_affineSpan_image (W j)
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

namespace Convex

open Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V} {K : Set V}

/-- On a convex set missing the singular support of a wall family, a wall meeting
the set contains every point of the set lying in the wall's affine span. -/
theorem inter_affineSpan_subset_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι}
    (hmeet : (K ∩ W j).Nonempty) : K ∩ affineSpan ℝ (W j) ⊆ W j := by
  apply hK.inter_affineSpan_subset hmeet
  exact disjoint_left.mpr fun x hx hf =>
    hKW.notMem_of_mem_left hx (mem_singularSupport.mpr (Or.inl ⟨j, hf⟩))

/-- On a convex set missing the singular support, a wall meeting the set at `p`
consists there of the points where a normal of its affine span takes its value at `p`. -/
theorem mem_iff_apply_eq_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j : ι}
    {ν : V →ₗ[ℝ] ℝ} (hν : LinearMap.ker ν = (affineSpan ℝ (W j)).direction)
    {p : V} (hpK : p ∈ K) (hpW : p ∈ W j) {v : V} (hv : v ∈ K) :
    v ∈ W j ↔ ν v = ν p := by
  have hp : p ∈ affineSpan ℝ (W j) := subset_affineSpan ℝ _ hpW
  have hiff : v ∈ affineSpan ℝ (W j) ↔ ν v = ν p := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp, ← hν, LinearMap.mem_ker,
      vsub_eq_sub, map_sub, sub_eq_zero]
  refine ⟨fun h => hiff.mp (subset_affineSpan ℝ _ h), fun h => ?_⟩
  exact hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW ⟨p, hpK, hpW⟩
    ⟨hv, hiff.mpr h⟩

/-- On a convex set missing the singular support, two walls with a common point
in the set agree on the set. -/
theorem mem_iff_mem_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j k : ι}
    {p : V} (hpK : p ∈ K) (hpj : p ∈ W j) (hpk : p ∈ W k) {v : V} (hv : v ∈ K) :
    v ∈ W j ↔ v ∈ W k := by
  have hdir : (affineSpan ℝ (W j)).direction = (affineSpan ℝ (W k)).direction := by
    by_contra hne
    exact hKW.notMem_of_mem_left hpK (mem_singularSupport.mpr (Or.inr ⟨j, k, hne, hpj, hpk⟩))
  have hspan := AffineSubspace.ext_of_direction_eq hdir
    ⟨p, subset_affineSpan ℝ _ hpj, subset_affineSpan ℝ _ hpk⟩
  have hsub {i : ι} (hpi : p ∈ W i) :
      v ∈ W i ↔ v ∈ affineSpan ℝ (W i) :=
    ⟨fun h => subset_affineSpan ℝ _ h, fun h =>
      hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW ⟨p, hpK, hpi⟩ ⟨hv, h⟩⟩
  rw [hsub hpj, hsub hpk, hspan]

/-- Two walls do not cross inside a convex set missing the singular support: the
normal of one wall does not change sign between two points of another wall in the set. -/
theorem sub_mul_sub_nonneg_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W)) {j k : ι}
    {ν : V →ₗ[ℝ] ℝ} (hν : LinearMap.ker ν = (affineSpan ℝ (W k)).direction)
    {p q r : V} (hpK : p ∈ K) (hpW : p ∈ W j) (hqK : q ∈ K) (hqW : q ∈ W j)
    (hrK : r ∈ K) (hrW : r ∈ W k) :
    0 ≤ (ν p - ν r) * (ν q - ν r) := by
  refine le_of_not_gt fun hneg => ?_
  have hrseg : ν r ∈ segment ℝ (ν p) (ν q) := by
    rw [segment_eq_Icc']
    rcases mul_neg_iff.mp hneg with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨(min_le_right _ _).trans (by linarith),
        (by linarith : ν r ≤ ν p).trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans (by linarith),
        (by linarith : ν r ≤ ν q).trans (le_max_right _ _)⟩
  have himage := image_segment ℝ ν.toAffineMap p q
  simp only [LinearMap.coe_toAffineMap] at himage
  rw [← himage] at hrseg
  obtain ⟨m, hmseg, hνm⟩ := hrseg
  have hmK : m ∈ K := hK.segment_subset hpK hqK hmseg
  have hmj : m ∈ W j := hK.inter_affineSpan_subset_of_disjoint_singularSupport hKW
    ⟨p, hpK, hpW⟩ ⟨hmK, (affineSpan ℝ (W j)).convex.segment_subset
      (subset_affineSpan ℝ _ hpW) (subset_affineSpan ℝ _ hqW) hmseg⟩
  have hmk : m ∈ W k :=
    (hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW hν hrK hrW hmK).mpr hνm
  have hpk : p ∈ W k := (hK.mem_iff_mem_of_disjoint_singularSupport hKW hmK hmj hmk
    hpK).mp hpW
  have ha : ν p - ν r = 0 := sub_eq_zero.mpr
    ((hK.mem_iff_apply_eq_of_disjoint_singularSupport hKW hν hrK hrW hpK).mp hpk)
  rw [ha, zero_mul] at hneg
  exact lt_irrefl _ hneg

end Convex
