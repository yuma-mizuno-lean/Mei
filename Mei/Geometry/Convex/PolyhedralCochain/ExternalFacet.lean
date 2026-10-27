/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Complex
public import Mei.Geometry.Convex.PolyhedralCochain.InternalFacet
public import Mei.Geometry.Convex.PolyhedralCochain.Boundary

/-!
# Signed boundaries under complex subdivision

The signed boundary of a cell equals the sum of the signed boundaries of its
pieces in a subdivision of finite polyhedral complexes. Internal occurrences
cancel, and every external occurrence is a piece of a unique coarse signed
facet, with the inherited orientation. Parent indices are retained throughout
the comparison, so no incidence multiplicity is lost.

The external matching uses `OrientedCell.boundary_subcell_internal_or_external`,
`OrientedCell.boundaryFacet_orientation_eq_of_subset`, and
`OrientedCell.existsUnique_boundaryFacet_of_mem_subdivisionPieces`. The final
identity combines this matching with
`OrientedCell.cellCoboundary_eq_sum_subdivisionPieces` and
`OrientedCell.IsOrientedSubdivision.sum_cellCoboundary_eq_sum_external_boundaryFacets`.
It is the subdivision identity for the generator coboundary when the
subdivision is induced by a finite complex; no coboundary on arbitrary cochain
classes is defined here. Unbounded cells and lineality are allowed.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {σ τ : OrientedCell h k} {υ ω : OrientedCell h (k + 1)}
  {C D : FinitePolyhedralComplex h}

/-- A refined boundary facet contained in a coarse boundary facet inherits
exactly its signed conormal orientation, and is one of its subdivision pieces. -/
theorem mem_subdivisionPieces_of_mem_boundaryFacets
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

/-- Each external signed facet of a refined parent is a subdivision piece of
exactly one signed coarse facet. This identifies its orientation as well as
its support. -/
theorem existsUnique_mem_subdivisionPieces_of_external_boundaryFacet
    (hτ : τ ∈ σ.subdivisionPieces C) (hυ : υ ∈ τ.boundaryFacets)
    (hfront : υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier) :
    ∃! ω : OrientedCell h (k + 1), ω ∈ σ.boundaryFacets ∧
      υ ∈ ω.subdivisionPieces C := by
  have := h.finiteDimensional
  have hsub := (τ.carrier_subset_of_mem_boundaryFacets hυ).trans
    ((σ.mem_subdivisionPieces C τ).mp hτ).2.1
  have hnot : ¬intrinsicInterior ℝ υ.carrier ⊆ intrinsicInterior ℝ σ.carrier := by
    intro hinto
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp υ.rational
    obtain ⟨x, hx⟩ := υ.nonempty.intrinsicInterior (hP ▸ P.convex)
    have hxb := hfront (intrinsicInterior_subset hx)
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hxb
    exact hxb.2 (hinto hx)
  obtain ⟨ω, ⟨hω, hυω⟩, huniq⟩ :=
    (σ.boundary_subcell_internal_or_external υ hsub).resolve_left hnot
  refine ⟨ω, ⟨hω, mem_subdivisionPieces_of_mem_boundaryFacets hτ hυ hω hυω⟩, ?_⟩
  rintro ξ ⟨hξ, hυξ⟩
  exact huniq ξ ⟨hξ, ((ξ.mem_subdivisionPieces C υ).mp hυξ).2.1⟩

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

open Classical in
private theorem sum_external_boundaryFacets_eq_sum_subdivisionPieces
    (hCD : C.IsSubdivision D) (hσ : σ.carrier ∈ D.cells) (c : E) :
    (∑ τ ∈ σ.subdivisionPieces C, ∑ υ ∈ τ.boundaryFacets with
      υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier, PolyhedralCochain.mk (R := R) υ c) =
      ∑ ω ∈ σ.boundaryFacets, ∑ υ ∈ ω.subdivisionPieces C,
        PolyhedralCochain.mk υ c := by
  classical
  let S := (σ.subdivisionPieces C).sigma fun τ => τ.boundaryFacets.filter fun υ =>
    υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier
  let T := σ.boundaryFacets.sigma fun ω => ω.subdivisionPieces C
  have hS (x : Σ _ : OrientedCell h k, OrientedCell h (k + 1)) :
      x ∈ S ↔ x.1 ∈ σ.subdivisionPieces C ∧ x.2 ∈ x.1.boundaryFacets ∧
        x.2.carrier ⊆ intrinsicFrontier ℝ σ.carrier := by
    simp only [S, Finset.mem_sigma, Finset.mem_filter]
  have hT (y : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1)) :
      y ∈ T ↔ y.1 ∈ σ.boundaryFacets ∧ y.2 ∈ y.1.subdivisionPieces C := by
    simp only [T, Finset.mem_sigma]
  have hex (x) (hx : x ∈ S) :=
    existsUnique_mem_subdivisionPieces_of_external_boundaryFacet
      ((hS x).mp hx).1 ((hS x).mp hx).2.1 ((hS x).mp hx).2.2
  let f (x) (hx : x ∈ S) : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1) :=
    ⟨(hex x hx).choose, x.2⟩
  have hf (x) (hx : x ∈ S) : f x hx ∈ T :=
    (hT _).mpr (hex x hx).choose_spec.1
  -- Match external occurrences by the signed refined facet. Its parent is
  -- unique among equally oriented cells in the common affine span.
  have hinj (x) (hx : x ∈ S) (y) (hy : y ∈ S) (he : f x hx = f y hy) : x = y := by
    have hxy : x.2 = y.2 := congrArg Sigma.snd he
    obtain ⟨hxQ, hxF, _⟩ := (hS x).mp hx
    obtain ⟨hyQ, hyF, _⟩ := (hS y).mp hy
    have hQ := σ.isOrientedSubdivision_subdivisionPieces hCD hσ
    have hp := C.eq_of_mem_boundaryFacets
      ((σ.mem_subdivisionPieces C x.1).mp hxQ).1
      ((σ.mem_subdivisionPieces C y.1).mp hyQ).1
      ((hQ.affineSpan_eq hxQ).trans (hQ.affineSpan_eq hyQ).symm)
      ((hQ.orientation_eq _ hxQ).trans (hQ.orientation_eq _ hyQ).symm)
      hxF (hxy ▸ hyF)
    exact Sigma.ext hp (heq_of_eq hxy)
  have hsurj (y) (hy : y ∈ T) : ∃ x hx, f x hx = y := by
    obtain ⟨hyF, hyQ⟩ := (hT y).mp hy
    obtain ⟨F, hF, hFn, hFd, hyeq⟩ := (σ.mem_boundaryFacets y.1).mp hyF
    obtain ⟨τ, ⟨hτ, hyτ⟩, _⟩ :=
      σ.existsUnique_boundaryFacet_of_mem_subdivisionPieces hCD hσ hF hFn hFd
        (hyeq ▸ hyQ)
    have hfront : y.2.carrier ⊆ intrinsicFrontier ℝ σ.carrier := by
      rw [σ.intrinsicFrontier_eq_biUnion_boundaryFacets]
      exact (((y.1.mem_subdivisionPieces C y.2).mp hyQ).2.1).trans
        (Set.subset_biUnion_of_mem (u := fun ω : OrientedCell h (k + 1) => ω.carrier) hyF)
    let x : Σ _ : OrientedCell h k, OrientedCell h (k + 1) := ⟨τ, y.2⟩
    have hx : x ∈ S := (hS x).mpr ⟨hτ, hyτ, hfront⟩
    refine ⟨x, hx, Sigma.ext ?_ (HEq.refl _)⟩
    exact ((hex x hx).choose_spec.2 y.1 ⟨hyF, hyQ⟩).symm
  rw [Finset.sum_sigma' (σ.subdivisionPieces C), Finset.sum_sigma' σ.boundaryFacets]
  exact Finset.sum_bij f hf hinj hsurj (fun _ _ => rfl)

/-- A subdivision of finite polyhedral complexes preserves the entire signed
boundary: the boundary of an original cell is the sum of the boundaries of
its same-codimension oriented pieces. -/
theorem cellCoboundary_eq_sum_cellCoboundary_subdivisionPieces
    (σ : OrientedCell h k) (hCD : C.IsSubdivision D) (hσ : σ.carrier ∈ D.cells) (c : E) :
    σ.cellCoboundary (R := R) c =
      ∑ τ ∈ σ.subdivisionPieces C, τ.cellCoboundary c := by
  classical
  have hQ := σ.isOrientedSubdivision_subdivisionPieces hCD hσ
  rw [hQ.sum_cellCoboundary_eq_sum_external_boundaryFacets
    (fun τ hτ => ((σ.mem_subdivisionPieces C τ).mp hτ).1)]
  exact (σ.cellCoboundary_eq_sum_subdivisionPieces hCD hσ c).trans
    (sum_external_boundaryFacets_eq_sum_subdivisionPieces hCD hσ c).symm

end Mei.OrientedCell
