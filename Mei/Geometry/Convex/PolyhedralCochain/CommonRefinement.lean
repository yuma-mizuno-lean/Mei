/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Complex
public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision

/-!
# Common complex presentations of polyhedral cochains

Every finite family of oriented cells admits simultaneous oriented subdivisions
on one finite ambient complex. Consequently every finite family of polyhedral
cochains admits finite presentations whose supports are cells of a single
complex. This permits geometric tests and coefficient comparisons to be made
on a common stratification, even when the original cells overlap or have
different tangent spaces.

The construction combines `FinitePolyhedralComplex.ambientSubdivision` with
`OrientedCell.subdivisionPieces`. The full-dimensional covering argument is
`FinitePolyhedralComplex.exists_mem_cells_subset_finrank_eq_of_cover`:
lower-dimensional pieces cannot cover a relative open neighborhood, and
closedness recovers boundary points. Cochain equality follows from the existing
oriented subdivision relation. Coefficients on identical oriented pieces are
added; opposite orientations are retained and no independence is asserted.
Unbounded supports, lineality, real offsets and modules over arbitrary rings
are allowed.
-/

public section

noncomputable section

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

namespace Mei.OrientedCell

/-- Any finite family of oriented cells can be subdivided simultaneously using
the cells of one finite complex. Each piece inherits its parent's orientation. -/
theorem exists_common_subdivision {ι : Type*} [Finite ι] (σ : ι → OrientedCell h k) :
    ∃ C : FinitePolyhedralComplex h, ∀ a,
      IsOrientedSubdivision (σ a) ((σ a).subdivisionPieces C) := by
  classical
  choose P hP using fun a => isRationalNormalPolyhedron_iff.mp (σ a).rational
  refine ⟨FinitePolyhedralComplex.ambientSubdivision P, fun a => ?_⟩
  apply (σ a).isOrientedSubdivision_subdivisionPieces_of_cover
  intro x hx
  obtain ⟨Q, hQ, hxQ, hsub⟩ :=
    FinitePolyhedralComplex.exists_mem_ambientSubdivision_cells_subset P a
      (by rwa [hP a])
  exact ⟨Q, hQ, by rwa [hP a] at hsub, hxQ⟩

end Mei.OrientedCell

open Mei PolyhedralCochain

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

namespace Finsupp

/-- A finite presentation can be refined onto a prescribed complex whenever
its supported cells admit the induced oriented subdivisions. The coefficient
of a repeated oriented piece is the sum of all its occurrences. -/
theorem exists_presentation_on_complex (f : OrientedCell h k →₀ E)
    (C : FinitePolyhedralComplex h)
    (hf : ∀ σ ∈ f.support,
      OrientedCell.IsOrientedSubdivision σ (σ.subdivisionPieces C)) :
    ∃ g : OrientedCell h k →₀ E, ofFinsupp (R := R) g = ofFinsupp f ∧
      ∀ τ ∈ g.support, τ.carrier ∈ C.cells := by
  classical
  let g : OrientedCell h k →₀ E :=
    ∑ σ ∈ f.support, ∑ τ ∈ σ.subdivisionPieces C, Finsupp.single τ (f σ)
  refine ⟨g, ?_, ?_⟩
  · conv_rhs => rw [← Finsupp.sum_single f]
    simp only [g, map_sum, ofFinsupp_single, Finsupp.sum]
    exact Finset.sum_congr rfl fun σ hσ =>
      (mk_eq_sum_of_isOrientedSubdivision (hf σ hσ) (f σ)).symm
  · intro τ hτ
    obtain ⟨σ, _, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    obtain ⟨υ, hυ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
    have he := ((Finsupp.mem_support_single _ _ _).mp hτ).1
    rw [he]
    exact ((σ.mem_subdivisionPieces C υ).mp hυ).1

end Finsupp

namespace Mei.PolyhedralCochain

/-- Every finite family of cochains has presentations supported on the cells
of one finite complex. Original supports may overlap, coincide, or have
different affine spans. No relation between the cochains is assumed. -/
theorem exists_common_complex_presentation {ι : Type*} [Finite ι]
    (x : ι → PolyhedralCochain R h E k) :
    ∃ (C : FinitePolyhedralComplex h) (f : ι → OrientedCell h k →₀ E),
      ∀ a, ofFinsupp (f a) = x a ∧ ∀ σ ∈ (f a).support, σ.carrier ∈ C.cells := by
  classical
  choose f hf using fun a => ofFinsupp_surjective (x a)
  obtain ⟨C, hC⟩ := OrientedCell.exists_common_subdivision
    (fun a : Σ a, (f a).support => a.2.val)
  have hex (a : ι) := (f a).exists_presentation_on_complex (R := R) C
    (fun σ hσ => hC ⟨a, ⟨σ, hσ⟩⟩)
  choose g hg using hex
  exact ⟨C, g, fun a => ⟨(hg a).1.trans (hf a), (hg a).2⟩⟩

end Mei.PolyhedralCochain
