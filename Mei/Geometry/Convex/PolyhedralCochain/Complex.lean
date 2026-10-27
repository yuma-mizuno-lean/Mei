/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Incidence
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision

/-!
# Oriented subdivisions induced by finite complexes

A subdivision of a finite polyhedral complex subdivides each oriented cell of the
original complex. The pieces inherit its conormal orientation. In particular this
applies to every signed boundary facet. Each piece of such a facet is the actual
signed boundary facet of a unique refined parent cell, with exactly the inherited
orientation. Consequently its cochain generator is the sum of these external
signed facets, including their boundary points. A facet of a refined piece whose
relative interior meets the original cell's relative interior has a unique
distinct parent inducing the opposite signed facet.

The covering and incidence arguments use
`FinitePolyhedralComplex.IsSubdivision.exists_mem_cells_subset_finrank_eq` and
`FinitePolyhedralComplex.subset_of_mem_intrinsicInterior`. The orientation comparison
uses `OrientedCell.boundaryFacet_orientation_eq_of_subset`. Internal incidence uses
`FinitePolyhedralComplex.eventually_subset_of_mem_cell`: a short ray beyond an
internal facet must enter another piece containing that facet. Opposite signs and
uniqueness use `FinitePolyhedralComplex.eq_reverse_of_mem_boundaryFacets`.
These are the local incidence statements needed to assemble cancellation of the
internal terms in the full coboundary sum.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

private def subdivisionCell (σ : OrientedCell h k) (C : FinitePolyhedralComplex h)
    (P : {P : Set V // P ∈ C.cellsOfCodimension k ∧ P ⊆ σ.carrier}) :
    OrientedCell h k := by
  have := h.finiteDimensional
  have hm := (C.mem_cellsOfCodimension k P).mp P.property.1
  have hd : (affineSpan ℝ P.val).direction = (affineSpan ℝ σ.carrier).direction := by
    apply Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ P.property.2))
    have hs := σ.finrank_direction_add
    omega
  exact
    { carrier := P.val
      rational := C.rational P hm.1
      nonempty := C.nonempty P hm.1
      finrank_direction_add := hm.2
      orientation := σ.orientation
      isConormal := hd ▸ σ.isConormal }

/-- The cells of a finite complex contained in an oriented cell and having the
same codimension, equipped with its orientation. -/
def subdivisionPieces (σ : OrientedCell h k) (C : FinitePolyhedralComplex h) :
    Finset (OrientedCell h k) := by
  classical
  let S := (C.cellsOfCodimension k).filter fun P => P ⊆ σ.carrier
  exact S.attach.image fun P => subdivisionCell σ C
    ⟨P.val, (Finset.mem_filter.mp P.property)⟩

/-- A subdivision piece is characterized by its geometric cell, containment and
inherited orientation. -/
@[simp]
theorem mem_subdivisionPieces (σ : OrientedCell h k) (C : FinitePolyhedralComplex h)
    (τ : OrientedCell h k) :
    τ ∈ σ.subdivisionPieces C ↔ τ.carrier ∈ C.cells ∧
      τ.carrier ⊆ σ.carrier ∧ τ.orientation = σ.orientation := by
  classical
  constructor
  · intro ht
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp ht
    have hm := Finset.mem_filter.mp P.property
    exact ⟨((C.mem_cellsOfCodimension k P).mp hm.1).1, hm.2, rfl⟩
  · rintro ⟨ht, hsub, ho⟩
    have hm : τ.carrier ∈ (C.cellsOfCodimension k).filter fun P => P ⊆ σ.carrier :=
      Finset.mem_filter.mpr ⟨(C.mem_cellsOfCodimension k _).mpr
        ⟨ht, τ.finrank_direction_add⟩, hsub⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨τ.carrier, hm⟩, Finset.mem_attach _ _, ?_⟩
    exact OrientedCell.ext rfl ho.symm

/-- A refined boundary facet contained in a coarse boundary facet inherits
exactly its signed conormal orientation, and is one of its subdivision pieces. -/
theorem mem_subdivisionPieces_of_mem_boundaryFacets
    {σ τ : OrientedCell h k} {υ ω : OrientedCell h (k + 1)}
    {C : FinitePolyhedralComplex h}
    (hτ : τ ∈ σ.subdivisionPieces C) (hυ : υ ∈ τ.boundaryFacets)
    (hω : ω ∈ σ.boundaryFacets) (hsub : υ.carrier ⊆ ω.carrier) :
    υ ∈ ω.subdivisionPieces C := by
  obtain ⟨hτC, hτσ, hτo⟩ := (σ.mem_subdivisionPieces C τ).mp hτ
  obtain ⟨F, hF, hFn, hFd, rfl⟩ := (τ.mem_boundaryFacets υ).mp hυ
  obtain ⟨G, hG, hGn, hGd, rfl⟩ := (σ.mem_boundaryFacets ω).mp hω
  simp only [boundaryFacet_carrier] at hsub
  apply (mem_subdivisionPieces _ C _).mpr
  refine ⟨?_, by simpa only [boundaryFacet_carrier] using hsub, ?_⟩
  · rw [boundaryFacet_carrier]
    exact C.face_closed τ.carrier hτC F (isPolyhedralFace_iff.mpr ⟨hFn, hF⟩)
  · exact σ.boundaryFacet_orientation_eq_of_subset τ hτσ hτo
      hG hGn hGd hF hFn hFd hsub

/-- A complex covering an oriented cell by contained cells gives an oriented
subdivision by its cells of the same codimension. -/
theorem isOrientedSubdivision_subdivisionPieces_of_cover (σ : OrientedCell h k)
    (C : FinitePolyhedralComplex h)
    (hcover : ∀ x ∈ σ.carrier, ∃ P ∈ C.cells, P ⊆ σ.carrier ∧ x ∈ P) :
    IsOrientedSubdivision σ (σ.subdivisionPieces C) := by
  classical
  refine ⟨?_, ?_, fun τ ht => ((σ.mem_subdivisionPieces C τ).mp ht).2.2⟩
  · apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨τ, ht, hx⟩ := Set.mem_iUnion₂.mp hx
      exact ((σ.mem_subdivisionPieces C τ).mp ht).2.1 hx
    · intro x hx
      obtain ⟨P, hP, hsub, hxP, hd⟩ :=
        C.exists_mem_cells_subset_finrank_eq_of_cover (by
          obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
          exact hP ▸ P.convex) hcover hx
      have hdim : finrank ℝ (affineSpan ℝ P).direction + k = finrank ℝ V := by
        rw [hd]
        exact σ.finrank_direction_add
      let τ := subdivisionCell σ C
        ⟨P, (C.mem_cellsOfCodimension k P).mpr ⟨hP, hdim⟩, hsub⟩
      exact Set.mem_iUnion₂.mpr ⟨τ,
        (σ.mem_subdivisionPieces C τ).mpr ⟨hP, hsub, rfl⟩, hxP⟩
  · intro τ ht υ hu hne
    obtain ⟨htC, _, hto⟩ := (σ.mem_subdivisionPieces C τ).mp ht
    obtain ⟨huC, _, huo⟩ := (σ.mem_subdivisionPieces C υ).mp hu
    exact C.disjoint_intrinsicInterior htC huC
      (fun he => hne (OrientedCell.ext he (hto.trans huo.symm)))

/-- A complex subdivision induces an oriented subdivision of every original cell. -/
theorem isOrientedSubdivision_subdivisionPieces (σ : OrientedCell h k)
    {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (hσ : σ.carrier ∈ D.cells) :
    IsOrientedSubdivision σ (σ.subdivisionPieces C) :=
  σ.isOrientedSubdivision_subdivisionPieces_of_cover C
    (fun _ hx => hCD.exists_mem_cells_subset hσ hx)

/-- Every external piece of a signed boundary facet occurs in exactly one refined
parent boundary, with its inherited orientation. -/
theorem existsUnique_boundaryFacet_of_mem_subdivisionPieces (σ : OrientedCell h k)
    {C : FinitePolyhedralComplex h}
    (hQ : IsOrientedSubdivision σ (σ.subdivisionPieces C)) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {τ : OrientedCell h (k + 1)}
    (hτ : τ ∈ (σ.boundaryFacet hF hne hdim).subdivisionPieces C) :
    ∃! υ : OrientedCell h k, υ ∈ σ.subdivisionPieces C ∧ τ ∈ υ.boundaryFacets := by
  have := h.finiteDimensional
  obtain ⟨hτC, hτF, ho⟩ :=
    ((σ.boundaryFacet hF hne hdim).mem_subdivisionPieces C τ).mp hτ
  rw [boundaryFacet_carrier] at hτF
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior
    (C.isConvexPolyhedron hτC).convex τ.nonempty
  obtain ⟨υ, hυ, hxP⟩ := Set.mem_iUnion₂.mp
    (hQ.biUnion_carrier ▸ hF.subset (hτF (intrinsicInterior_subset hx)))
  obtain ⟨hP, hsub, hυo⟩ := (σ.mem_subdivisionPieces C υ).mp hυ
  have hτP : τ.carrier ⊆ υ.carrier := C.subset_of_mem_intrinsicInterior hτC hP hx hxP
  have he : IsExposed ℝ υ.carrier τ.carrier :=
    (isPolyhedralFace_iff.mp (C.face_of_subset hτC hP hτP)).2
  have hdf : finrank ℝ (vectorSpan ℝ τ.carrier) + 1 =
      finrank ℝ (vectorSpan ℝ υ.carrier) := by
    have ht := τ.finrank_direction_add
    have hv := υ.finrank_direction_add
    rw [direction_affineSpan] at ht hv
    omega
  have hτeq : τ = υ.boundaryFacet he τ.nonempty hdf := by
    apply OrientedCell.ext (by simp)
    exact ho.trans (σ.boundaryFacet_orientation_eq_of_subset υ hsub hυo
      hF hne hdim he τ.nonempty hdf hτF).symm
  have hτmem : τ ∈ υ.boundaryFacets := by
    rw [hτeq]
    exact υ.boundaryFacet_mem_boundaryFacets he τ.nonempty hdf
  refine ⟨υ, ⟨hυ, hτmem⟩, ?_⟩
  intro ω hω
  obtain ⟨hωC, _, hωo⟩ := (σ.mem_subdivisionPieces C ω).mp hω.1
  exact C.eq_of_mem_boundaryFacets hωC hP
    ((hQ.affineSpan_eq hω.1).trans (hQ.affineSpan_eq hυ).symm)
    (hωo.trans ((σ.mem_subdivisionPieces C υ).mp hυ).2.2.symm) hω.2 hτmem

/-- A complex subdividing a cell also subdivides each signed boundary facet,
with its inherited orientation. -/
theorem isOrientedSubdivision_boundaryFacet_subdivisionPieces (σ : OrientedCell h k)
    {C : FinitePolyhedralComplex h}
    (hQ : IsOrientedSubdivision σ (σ.subdivisionPieces C))
    {τ : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets) :
    IsOrientedSubdivision τ (τ.subdivisionPieces C) := by
  obtain ⟨F, hF, hne, hd, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
  apply isOrientedSubdivision_subdivisionPieces_of_cover
  intro x hx
  rw [boundaryFacet_carrier] at hx
  obtain ⟨υ, hυ, hxυ⟩ := Set.mem_iUnion₂.mp (hQ.biUnion_carrier ▸ hF.subset hx)
  obtain ⟨hυC, hυσ, _⟩ := (σ.mem_subdivisionPieces C υ).mp hυ
  have hface : IsExposed ℝ υ.carrier (F ∩ υ.carrier) := by
    simpa only [Set.inter_eq_right.mpr hυσ] using hF.inter_inter (IsExposed.refl υ.carrier)
  exact ⟨F ∩ υ.carrier, C.face_closed υ.carrier hυC _
      (isPolyhedralFace_iff.mpr ⟨⟨x, hx, hxυ⟩, hface⟩),
    by simp only [boundaryFacet_carrier]; exact Set.inter_subset_left, ⟨hx, hxυ⟩⟩

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Refine the entire signed boundary sum into external pieces in a complex
subdivision. Every summand is a signed facet of a refined parent, by
`existsUnique_boundaryFacet_of_mem_subdivisionPieces`. -/
theorem cellCoboundary_eq_sum_subdivisionPieces (σ : OrientedCell h k)
    {C : FinitePolyhedralComplex h}
    (hQ : IsOrientedSubdivision σ (σ.subdivisionPieces C)) (c : E) :
    σ.cellCoboundary (R := R) c =
      ∑ τ ∈ σ.boundaryFacets, ∑ υ ∈ τ.subdivisionPieces C, PolyhedralCochain.mk υ c := by
  classical
  rw [cellCoboundary_apply]
  exact Finset.sum_congr rfl fun τ hτ => PolyhedralCochain.mk_eq_sum_of_isOrientedSubdivision
    (σ.isOrientedSubdivision_boundaryFacet_subdivisionPieces hQ hτ) c

open Filter Topology in
/-- An internal facet of a refined piece has exactly one opposite incidence.
Internality is witnessed by a relative interior point of the facet lying in
the relative interior of the original cell. This works in every codimension,
including subdivisions of lower-dimensional cells. -/
theorem existsUnique_reverse_boundaryFacet_of_mem_intrinsicInterior (σ : OrientedCell h k)
    {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (hσ : σ.carrier ∈ D.cells) {τ : OrientedCell h k}
    (hτ : τ ∈ σ.subdivisionPieces C) {ξ : OrientedCell h (k + 1)}
    (hξ : ξ ∈ τ.boundaryFacets) {q : V}
    (hqξ : q ∈ intrinsicInterior ℝ ξ.carrier)
    (hqσ : q ∈ intrinsicInterior ℝ σ.carrier) :
    ∃! υ : OrientedCell h k, υ ∈ σ.subdivisionPieces C ∧
      υ ≠ τ ∧ ξ.reverse ∈ υ.boundaryFacets := by
  classical
  have := h.finiteDimensional
  have hQ := σ.isOrientedSubdivision_subdivisionPieces hCD hσ
  obtain ⟨hτC, hτσ, hτo⟩ := (σ.mem_subdivisionPieces C τ).mp hτ
  obtain ⟨F, hF, hFne, hFdim, hξF⟩ := (τ.mem_boundaryFacets ξ).mp hξ
  have hc : ξ.carrier = F := hξF ▸ τ.boundaryFacet_carrier hF hFne hFdim
  have hξC : ξ.carrier ∈ C.cells := by
    rw [hc]
    exact C.face_closed τ.carrier hτC F (isPolyhedralFace_iff.mpr ⟨hFne, hF⟩)
  have hproper : F ≠ τ.carrier := by
    intro he
    rw [he] at hFdim
    omega
  obtain ⟨x, hxτ, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  have hqF : q ∈ F := hc ▸ intrinsicInterior_subset hqξ
  obtain ⟨l, hl⟩ := hF hFne
  have hqmax := (Set.ext_iff.mp hl q).mp hqF
  have hlt : l x < l q := lt_of_le_of_ne (hqmax.2 x hxτ) (fun he =>
    hxF ((Set.ext_iff.mp hl x).mpr ⟨hxτ, fun y hy => he ▸ hqmax.2 y hy⟩))
  -- Move beyond the facet, away from an interior-side point of the first piece.
  -- The original cell still contains the short ray, and all encountered cells contain the facet.
  let f : ℝ → V := fun t => q + t • (q - x)
  have htend : Tendsto f (𝓝 0) (𝓝 q) := by
    have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [f, zero_smul, add_zero] using hf.tendsto 0
  have hspan (t : ℝ) : f t ∈ affineSpan ℝ σ.carrier := by
    have hqA := subset_affineSpan ℝ _ (intrinsicInterior_subset hqσ)
    have hxA := subset_affineSpan ℝ _ (hτσ hxτ)
    simpa only [f, vadd_eq_add, vsub_eq_sub, add_comm] using
      (affineSpan ℝ σ.carrier).smul_vsub_vadd_mem t hqA hxA hqA
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ σ.carrier :=
    (tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall hspan⟩).eventually
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hqσ)
  have hnear := (hmem.and
    (htend.eventually (C.eventually_subset_of_mem_cell hξC hqξ))).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨t, ⟨htσ, htinc⟩, htpos⟩ :=
    (hnear.and (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t)).exists
  obtain ⟨υ, hυ, hftυ⟩ := Set.mem_iUnion₂.mp (hQ.biUnion_carrier ▸ htσ)
  obtain ⟨hυC, _, hυo⟩ := (σ.mem_subdivisionPieces C υ).mp hυ
  have hsub : ξ.carrier ⊆ υ.carrier := htinc _ hυC hftυ
  have hnot : f t ∉ τ.carrier := by
    intro hftτ
    have hle := hqmax.2 (f t) hftτ
    have he : l (f t) = l q + t * (l q - l x) := by
      simp only [f, map_add, map_smul, map_sub, smul_eq_mul]
    rw [he] at hle
    have := mul_pos htpos (sub_pos.mpr hlt)
    linarith
  have hne : τ.carrier ≠ υ.carrier := fun he => hnot (he ▸ hftυ)
  have hr := C.reverse_mem_boundaryFacets_of_subset hτC hυC hne
    ((hQ.affineSpan_eq hτ).trans (hQ.affineSpan_eq hυ).symm)
    (hτo.trans hυo.symm) hξ hsub
  refine ⟨υ, ⟨hυ, fun he => hne (congrArg carrier he).symm, hr⟩, ?_⟩
  intro ω hω
  obtain ⟨hωC, _, hωo⟩ := (σ.mem_subdivisionPieces C ω).mp hω.1
  exact C.eq_of_mem_boundaryFacets hωC hυC
    ((hQ.affineSpan_eq hω.1).trans (hQ.affineSpan_eq hυ).symm)
    (hωo.trans hυo.symm) hω.2.2 hr

end Mei.OrientedCell
