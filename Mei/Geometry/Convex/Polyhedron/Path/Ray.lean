/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mei.Geometry.Convex.Sweep.Exceptional

/-!
# Admissible backward segments in prescribed directions

For a finite indexed family of codimension-one polyhedra and finitely many
directions, an exceptional arrangement makes every sufficiently long backward
segment from a generic endpoint admissible. The distant endpoint eventually
misses every wall. Tangent walls are missed by the entire line, and zero
directions give constant admissible segments. Repeated supports are permitted.

The arrangement combines the supporting wall hyperplanes with the swept affine
cover supplied by `Convex.exists_finite_singularSupport_cover`, using
`ExceptionalArrangement.ofSweeps`. This supplies the straight backward portions
used in the coefficient recursion of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι]

/-- A finite arrangement ensures that, in each prescribed direction, every
sufficiently distant starting point gives an admissible segment to the generic
endpoint. No transversality condition is imposed on walls the line misses. -/
theorem exists_ray_admissibilityArrangement
    (W : ι → Set V) (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V) (vectors : Finset V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∃ y : WallComplement W, y.val = Q ∧ ∀ v ∈ vectors,
        ∀ᶠ T : ℝ in atTop, ∃ x : WallComplement W,
          x.val = Q + T • v ∧ WallComplement.AdmissibleSegment x y := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨S, hcover, hS⟩ := exists_finite_singularSupport_cover W hpoly hdim
  let cells := S.image (fun B : AffineSubspace ℝ V => (B : Set V))
  have hcells : ∀ P ∈ cells, P.Nonempty →
      Module.finrank ℝ (vectorSpan ℝ P) + 1 < Module.finrank ℝ V := by
    intro P hP _
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hP
    rw [← direction_affineSpan, AffineSubspace.affineSpan_coe]
    exact hS B hB
  let A : ExceptionalArrangement V :=
    ⟨Finset.univ.image (fun j => affineSpan ℝ (W j)), by
      rintro B hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      exact (affineSpan ℝ (W j)).ne_top_of_finrank_direction_add_one_eq (hdim j)⟩
  refine ⟨A.union (ExceptionalArrangement.ofSweeps cells vectors hcells), ?_⟩
  intro Q hQ
  obtain ⟨hwall, hsweep⟩ := ExceptionalArrangement.isGeneric_union.mp hQ
  have hQspan (j : ι) : Q ∉ affineSpan ℝ (W j) :=
    ExceptionalArrangement.isGeneric_iff.mp hwall _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  let y : WallComplement W := ⟨Q, fun j hj => hQspan j (subset_affineSpan ℝ _ hj)⟩
  refine ⟨y, rfl, fun v hv => ?_⟩
  have hregular (t : ℝ) : Q + t • v ∉ singularSupport W := by
    intro ht
    obtain ⟨B, hB, htB⟩ := Set.mem_iUnion₂.mp (hcover ht)
    exact (ExceptionalArrangement.isGeneric_ofSweeps_iff cells vectors hcells Q).mp hsweep
      (B : Set V) (Finset.mem_image.mpr ⟨B, hB, rfl⟩) v hv t
      (by rw [AffineSubspace.affineSpan_coe]; exact htB)
  have htrans (j : ι) {t : ℝ} (ht : Q + t • v ∈ W j) :
      v ∉ (affineSpan ℝ (W j)).direction := by
    intro hvj
    have hm := AffineSubspace.vadd_mem_of_mem_direction
      ((affineSpan ℝ (W j)).direction.smul_mem (-t) hvj) (subset_affineSpan ℝ _ ht)
    have he : (-t) • v +ᵥ (Q + t • v) = Q := by
      simp only [vadd_eq_add]
      module
    exact hQspan j (he ▸ hm)
  -- Each wall has at most one encounter parameter, so all distant points are allowed.
  have hfinite (j : ι) : {t : ℝ | Q + t • v ∈ W j}.Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    apply (affineSpan ℝ (W j)).subsingleton_preimage_lineMap
      (x := Q) (y := v +ᵥ Q) (by simpa using htrans j hs)
    · rw [mem_preimage, AffineMap.lineMap_vadd_apply]
      exact subset_affineSpan ℝ (W j)
        (by simpa only [mem_ofPred_eq, vadd_eq_add, add_comm] using hs)
    · rw [mem_preimage, AffineMap.lineMap_vadd_apply]
      exact subset_affineSpan ℝ (W j)
        (by simpa only [mem_ofPred_eq, vadd_eq_add, add_comm] using ht)
  have hfar : ∀ᶠ T : ℝ in atTop, ∀ j, Q + T • v ∉ W j := by
    apply eventually_all.mpr
    intro j
    obtain ⟨b, hb⟩ := (hfinite j).bddAbove
    filter_upwards [eventually_gt_atTop b] with T hT hmem
    exact (not_le_of_gt hT) (hb hmem)
  filter_upwards [hfar] with T hT
  let x : WallComplement W := ⟨Q + T • v, hT⟩
  have hline (s : ℝ) : AffineMap.lineMap x.val y.val s = Q + ((1 - s) * T) • v := by
    simp only [x, y, AffineMap.lineMap_apply_module']
    module
  refine ⟨x, rfl, (convex_segment x.val y.val).admissibleSegment_of_disjoint_singularSupport
    ?_ (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)⟩
  apply Set.disjoint_left.mpr
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨s, _, rfl⟩ := hz
  rw [hline]
  exact hregular _

end Mei.Convex
