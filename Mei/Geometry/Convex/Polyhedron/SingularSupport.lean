/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.SingularSupport
public import Mei.Geometry.Convex.Polyhedron.Boundary
public import Mei.Geometry.Affine.Codimension
public import Mei.Geometry.Affine.Span
import Mei.Analysis.Convex.Intrinsic

/-!
# Singular support under wall covers and products

We use the TauCeti singular support of an indexed wall family. This file studies
tangential motion near its complement and its behavior under covers and cylinders.
-/

public section

open TauCeti (singularSupport mem_singularSupport mem_intrinsicInterior_of_notMem_singularSupport)

open Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open Filter Topology in
/-- Near a regular point, displacements in a submodule tangent to every incident
wall preserve the entire set of incident indices. Closedness excludes nonincident
walls, while relative interior controls the incident ones. -/
theorem eventually_mem_iff_of_submodule_le_direction [Finite ι]
    (W : ι → Set V) (hclosed : ∀ j, IsClosed (W j)) (x : V)
    (hx : x ∉ singularSupport W) (S : Submodule ℝ V)
    (hS : ∀ j, x ∈ W j → S ≤ (affineSpan ℝ (W j)).direction) :
    ∀ᶠ w : S in 𝓝 0, ∀ j, x + (w : V) ∈ W j ↔ x ∈ W j := by
  apply eventually_all.mpr
  intro j
  have ht : Tendsto (fun w : S => x + (w : V)) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun w : S => x + (w : V)) := by fun_prop
    simpa using hc.tendsto (0 : S)
  by_cases hj : x ∈ W j
  · have hspan (w : S) : x + (w : V) ∈ affineSpan ℝ (W j) := by
      simpa only [vadd_eq_add, add_comm] using
        (affineSpan ℝ (W j)).vadd_mem_of_mem_direction (hS j hj w.property)
          (subset_affineSpan ℝ _ hj)
    have hwithin := tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hspan⟩
    filter_upwards [hwithin.eventually
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior
        (mem_intrinsicInterior_of_notMem_singularSupport hj hx))] with w hw
    exact iff_of_true hw hj
  · filter_upwards [ht.eventually ((hclosed j).isOpen_compl.mem_nhds hj)] with w hw
    exact iff_of_false hw hj

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

/-- Transport singular support along an affine equivalence with the same index set. -/
@[simp]
theorem singularSupport_image {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (W : ι → Set V) (e : V ≃ᴬ[ℝ] U) :
    singularSupport (fun i => e '' W i) = e '' singularSupport W :=
  e.singularSupport_image (Equiv.refl ι) (fun _ => rfl)

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

end Mei.Convex

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
