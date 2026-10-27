/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.CommonRefinement
public import Mei.Geometry.Convex.PolyhedralCochain.ExternalFacet

/-!
# Common complex refinements of oriented subdivisions

If a finite polyhedral complex subdivides every piece of an oriented
subdivision, its cells of the same codimension as the parent, equipped with
the parent's inherited orientation and contained in the parent, are exactly
the disjoint union of those contained in the pieces. Every such refined cell
is therefore counted once. This gives the reindexing needed to pass
from identities on a common complex to identities under arbitrary oriented
subdivision. Consequently the signed coboundary respects arbitrary oriented
subdivisions, including subdivisions whose pieces do not meet face to face.
Unbounded supports and lineality are allowed.
-/

/-
The proof uses `OrientedCell.subdivisionPieces` and
`FinitePolyhedralComplex.subset_of_mem_intrinsicInterior` to identify a cell
containing a relative interior point. Uniqueness follows from
`Mei.intrinsicInterior_mono_of_affineSpan_eq` and the original subdivision's
disjoint relative interiors. The boundary comparison uses
`OrientedCell.exists_common_subdivision` and
`OrientedCell.cellCoboundary_eq_sum_cellCoboundary_subdivisionPieces`.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell.IsOrientedSubdivision

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {σ : OrientedCell h k} {Q : Finset (OrientedCell h k)}

/-- The cells of a fixed complex of the same codimension as the parent, equipped
with the parent's inherited orientation and contained in distinct pieces of an
oriented subdivision, form disjoint finite families of oriented cells. -/
theorem pairwiseDisjoint_subdivisionPieces (hQ : IsOrientedSubdivision σ Q)
    (C : FinitePolyhedralComplex h) :
    (Q : Set (OrientedCell h k)).PairwiseDisjoint fun τ => τ.subdivisionPieces C := by
  have := h.finiteDimensional
  intro τ hτ υ hυ hne
  apply Finset.disjoint_left.mpr
  intro η hητ hηυ
  obtain ⟨_, hητ, _⟩ := (τ.mem_subdivisionPieces C η).mp hητ
  obtain ⟨_, hηυ, _⟩ := (υ.mem_subdivisionPieces C η).mp hηυ
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp η.rational
  obtain ⟨x, hx⟩ := η.nonempty.intrinsicInterior (hP ▸ P.convex)
  have hspanτ : affineSpan ℝ η.carrier = affineSpan ℝ τ.carrier := by
    obtain ⟨y, hy⟩ := η.nonempty
    exact AffineSubspace.ext_of_direction_eq (η.direction_eq_of_subset τ hητ)
      ⟨y, subset_affineSpan ℝ _ hy, subset_affineSpan ℝ _ (hητ hy)⟩
  have hspanυ : affineSpan ℝ η.carrier = affineSpan ℝ υ.carrier :=
    hspanτ.trans ((hQ.affineSpan_eq hτ).trans (hQ.affineSpan_eq hυ).symm)
  exact Set.disjoint_left.mp (hQ.pairwiseDisjoint hτ hυ hne)
    (Mei.intrinsicInterior_mono_of_affineSpan_eq hητ hspanτ hx)
    (Mei.intrinsicInterior_mono_of_affineSpan_eq hηυ hspanυ hx)

open Classical in
/-- If one complex subdivides all the pieces of an oriented subdivision, its
cells of the same codimension as the parent, equipped with the parent's inherited
orientation and contained in the parent, are precisely the union of those contained
in the pieces. The union is disjoint by `pairwiseDisjoint_subdivisionPieces`.
No face-incidence condition on the original pieces is needed. -/
theorem subdivisionPieces_eq_biUnion (hQ : IsOrientedSubdivision σ Q)
    (C : FinitePolyhedralComplex h)
    (hC : ∀ τ ∈ Q, IsOrientedSubdivision τ (τ.subdivisionPieces C)) :
    σ.subdivisionPieces C = Q.biUnion (fun τ => τ.subdivisionPieces C) := by
  have := h.finiteDimensional
  classical
  ext η
  simp only [Finset.mem_biUnion]
  constructor
  · intro hη
    obtain ⟨hηC, hησ, hηo⟩ := (σ.mem_subdivisionPieces C η).mp hη
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp η.rational
    obtain ⟨x, hx⟩ := η.nonempty.intrinsicInterior (hP ▸ P.convex)
    obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.mp
      (hQ.biUnion_carrier ▸ hησ (intrinsicInterior_subset hx))
    obtain ⟨υ, hυ, hxυ⟩ := Set.mem_iUnion₂.mp ((hC τ hτ).biUnion_carrier ▸ hxτ)
    obtain ⟨hυC, hυτ, hυo⟩ := (τ.mem_subdivisionPieces C υ).mp hυ
    have hηυ : η.carrier ⊆ υ.carrier :=
      C.subset_of_mem_intrinsicInterior hηC hυC hx hxυ
    have he : η.carrier = υ.carrier := by
      apply (isPolyhedralFace_iff.mp (C.face_of_subset hηC hυC hηυ)).2.eq_of_finrank_vectorSpan_eq
        η.nonempty
      have hηdim := η.finrank_direction_add
      have hυdim := υ.finrank_direction_add
      rw [direction_affineSpan] at hηdim hυdim
      omega
    exact ⟨τ, hτ, (τ.mem_subdivisionPieces C η).mpr
      ⟨hηC, he ▸ hυτ, hηo.trans (hQ.orientation_eq τ hτ).symm⟩⟩
  · rintro ⟨τ, hτ, hητ⟩
    obtain ⟨hηC, hητ, hηo⟩ := (τ.mem_subdivisionPieces C η).mp hητ
    exact (σ.mem_subdivisionPieces C η).mpr
      ⟨hηC, hητ.trans (hQ.carrier_subset hτ), hηo.trans (hQ.orientation_eq τ hτ)⟩

end Mei.OrientedCell.IsOrientedSubdivision

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The signed facet sum respects every oriented subdivision. The original
pieces need not be cells of a common complex or meet along whole faces. -/
theorem cellCoboundary_eq_sum_of_isOrientedSubdivision {σ : OrientedCell h k}
    {Q : Finset (OrientedCell h k)} (hQ : IsOrientedSubdivision σ Q) (c : E) :
    σ.cellCoboundary (R := R) c = ∑ τ ∈ Q, τ.cellCoboundary c := by
  classical
  obtain ⟨C, hC⟩ := exists_common_subdivision (fun a : Option Q =>
    a.elim σ (fun τ => τ.val))
  have hpieces := hQ.subdivisionPieces_eq_biUnion C
    (fun τ hτ => hC (some ⟨τ, hτ⟩))
  calc
    σ.cellCoboundary c = ∑ υ ∈ σ.subdivisionPieces C, υ.cellCoboundary c :=
      σ.cellCoboundary_eq_sum_cellCoboundary_subdivisionPieces (hC none) c
    _ = ∑ τ ∈ Q, ∑ υ ∈ τ.subdivisionPieces C, υ.cellCoboundary c := by
      rw [hpieces, Finset.sum_biUnion (hQ.pairwiseDisjoint_subdivisionPieces C)]
    _ = ∑ τ ∈ Q, τ.cellCoboundary c := Finset.sum_congr rfl fun τ hτ =>
      (τ.cellCoboundary_eq_sum_cellCoboundary_subdivisionPieces (hC (some ⟨τ, hτ⟩)) c).symm

end Mei.OrientedCell
