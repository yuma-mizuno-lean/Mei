/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision

/-!
# Oriented subdivisions induced by finite complexes

A subdivision of a finite polyhedral complex subdivides each oriented cell of the
original complex. The pieces inherit its conormal orientation. In particular this
applies to every signed boundary facet. Each piece of such a facet is the actual
signed boundary facet of some refined parent cell, with exactly the inherited
orientation. Consequently its cochain generator is the sum of these external
signed facets, including their boundary points.

The covering and incidence arguments use
`FinitePolyhedralComplex.IsSubdivision.exists_mem_cells_subset_finrank_eq` and
`FinitePolyhedralComplex.subset_of_mem_intrinsicInterior`. The orientation comparison
uses `OrientedCell.boundaryFacet_orientation_eq_of_subset`. This supplies the
external boundary comparison for subdivision; cancellation of internal facets is
a separate requirement for descending the full coboundary.
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

/-- A complex subdivision induces an oriented subdivision of every original cell. -/
theorem isOrientedSubdivision_subdivisionPieces (σ : OrientedCell h k)
    {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (hσ : σ.carrier ∈ D.cells) :
    IsOrientedSubdivision σ (σ.subdivisionPieces C) := by
  classical
  refine ⟨?_, ?_, fun τ ht => ((σ.mem_subdivisionPieces C τ).mp ht).2.2⟩
  · apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨τ, ht, hx⟩ := Set.mem_iUnion₂.mp hx
      exact ((σ.mem_subdivisionPieces C τ).mp ht).2.1 hx
    · intro x hx
      obtain ⟨P, hP, hsub, hxP, hd⟩ :=
        hCD.exists_mem_cells_subset_finrank_eq hσ hx
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

/-- Every external piece of a signed boundary facet is a signed boundary facet
of an actual refined parent cell. The refined parent inherits the original
orientation, so no orientation signs are chosen independently. -/
theorem exists_boundaryFacet_of_mem_subdivisionPieces (σ : OrientedCell h k)
    {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (hσ : σ.carrier ∈ D.cells) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {τ : OrientedCell h (k + 1)}
    (hτ : τ ∈ (σ.boundaryFacet hF hne hdim).subdivisionPieces C) :
    ∃ υ ∈ σ.subdivisionPieces C,
      ∃ (he : IsExposed ℝ υ.carrier τ.carrier)
        (hd : finrank ℝ (vectorSpan ℝ τ.carrier) + 1 =
          finrank ℝ (vectorSpan ℝ υ.carrier)),
        τ = υ.boundaryFacet he τ.nonempty hd := by
  have := h.finiteDimensional
  obtain ⟨hτC, hτF, ho⟩ :=
    ((σ.boundaryFacet hF hne hdim).mem_subdivisionPieces C τ).mp hτ
  rw [boundaryFacet_carrier] at hτF
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior
    (C.isConvexPolyhedron hτC).convex τ.nonempty
  obtain ⟨P, hP, hsub, hxP, hd⟩ := hCD.exists_mem_cells_subset_finrank_eq hσ
    (hF.subset (hτF (intrinsicInterior_subset hx)))
  have hdimP : finrank ℝ (affineSpan ℝ P).direction + k = finrank ℝ V := by
    rw [hd]
    exact σ.finrank_direction_add
  let υ := subdivisionCell σ C
    ⟨P, (C.mem_cellsOfCodimension k P).mpr ⟨hP, hdimP⟩, hsub⟩
  have hυ : υ ∈ σ.subdivisionPieces C :=
    (σ.mem_subdivisionPieces C υ).mpr ⟨hP, hsub, rfl⟩
  have hτP : τ.carrier ⊆ P := C.subset_of_mem_intrinsicInterior hτC hP hx hxP
  have he : IsExposed ℝ υ.carrier τ.carrier :=
    (isPolyhedralFace_iff.mp (C.face_of_subset hτC hP hτP)).2
  have hdf : finrank ℝ (vectorSpan ℝ τ.carrier) + 1 =
      finrank ℝ (vectorSpan ℝ υ.carrier) := by
    have ht := τ.finrank_direction_add
    have hv := υ.finrank_direction_add
    rw [direction_affineSpan] at ht hv
    omega
  refine ⟨υ, hυ, he, hdf, OrientedCell.ext (by simp) ?_⟩
  exact ho.trans (σ.boundaryFacet_orientation_eq_of_subset υ hsub rfl
    hF hne hdim he τ.nonempty hdf hτF).symm

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Refine the entire signed boundary sum into external pieces in a complex
subdivision. Every summand is a signed facet of a refined parent, by
`exists_boundaryFacet_of_mem_subdivisionPieces`. -/
theorem cellCoboundary_eq_sum_subdivisionPieces (σ : OrientedCell h k)
    {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (hσ : σ.carrier ∈ D.cells) (c : E) :
    σ.cellCoboundary (R := R) c =
      ∑ τ ∈ σ.boundaryFacets, ∑ υ ∈ τ.subdivisionPieces C, PolyhedralCochain.mk υ c := by
  classical
  rw [cellCoboundary_apply]
  apply Finset.sum_congr rfl
  intro τ hτ
  apply PolyhedralCochain.mk_eq_sum_of_isOrientedSubdivision
  apply τ.isOrientedSubdivision_subdivisionPieces hCD
  obtain ⟨F, hF, hne, hdim, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
  rw [boundaryFacet_carrier]
  exact D.face_closed σ.carrier hσ F (isPolyhedralFace_iff.mpr ⟨hne, hF⟩)

end Mei.OrientedCell
