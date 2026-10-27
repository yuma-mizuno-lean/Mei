/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Face.Intersection
public import Mei.Analysis.Convex.Exposed

/-!
# Facets of half-space cuts

Every nonempty exposed face of an affine half-space is either the whole half-space or its
boundary hyperplane. Consequently, cutting a polyhedron without decreasing its affine
dimension creates just one possible new facet: the section by the cutting hyperplane.
Every other facet is the intersection of an original facet with the half-space.

`TauCeti.IsConvexPolyhedron.facet_cut_iff` gives both directions of this classification.
It applies in the affine span of the original polyhedron, allowing lower-dimensional supports,
unboundedness, lineality, redundant inequalities and constant cutting functionals.
This exhaustiveness is needed when comparing signed facet sums before and after subdivision
by a hyperplane.

The classification uses `IsExposed.exists_inter_of_isConvexPolyhedron` to split a face of an
intersection, `IsExposed.eq_setOf_active` for the single defining inequality of a half-space,
and `IsExposed.eq_of_finrank_vectorSpan_eq` to identify nested faces of equal dimension.
-/

public section

open Set Module

namespace TauCeti.IsConvexPolyhedron

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P F : Set V}

/-- Exhaustive characterization of the nonempty facets of a half-space cut that preserves
affine dimension. The dimension hypothesis on `F` discards empty or lower-dimensional
restrictions of original facets automatically. No full-dimensionality or boundedness is
required of the original polyhedron. -/
theorem facet_cut_iff (hP : TauCeti.IsConvexPolyhedron P) (g : V →ᴬ[ℝ] ℝ)
    (hne : F.Nonempty)
    (hcut : finrank ℝ (vectorSpan ℝ (P ∩ {x | g x ≤ 0})) =
      finrank ℝ (vectorSpan ℝ P))
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P)) :
    IsExposed ℝ (P ∩ {x | g x ≤ 0}) F ↔
      F = P ∩ {x | g x = 0} ∨
        ∃ G, IsExposed ℝ P G ∧
          finrank ℝ (vectorSpan ℝ G) + 1 = finrank ℝ (vectorSpan ℝ P) ∧
          F = G ∩ {x | g x ≤ 0} := by
  constructor
  · intro hF
    obtain ⟨G, H, hG, hH, hGne, hHne, heq⟩ :=
      hF.exists_inter_of_isConvexPolyhedron hP
        (TauCeti.isConvexPolyhedron_setOf_le g) hne
    by_cases hGP : G = P
    · rcases hH.eq_halfspace_or_zero hHne with hHwhole | hHzero
      · have he : F = P ∩ {x | g x ≤ 0} := by rw [heq, hGP, hHwhole]
        rw [he, hcut] at hdim
        omega
      · exact Or.inl (by rw [heq, hGP, hHzero])
    · right
      have hFG : F ⊆ G := by rw [heq]; exact inter_subset_left
      have hFGdim := Submodule.finrank_mono (vectorSpan_mono ℝ hFG)
      have hGPdim := Submodule.finrank_mono (vectorSpan_mono ℝ hG.subset)
      have hGlt : finrank ℝ (vectorSpan ℝ G) < finrank ℝ (vectorSpan ℝ P) := by
        by_contra! hn
        exact hGP (hG.eq_of_finrank_vectorSpan_eq hGne (by omega))
      have hGdim : finrank ℝ (vectorSpan ℝ G) + 1 =
          finrank ℝ (vectorSpan ℝ P) := by omega
      refine ⟨G, hG, hGdim, ?_⟩
      have hinside : F ⊆ G ∩ {x | g x ≤ 0} :=
        fun x hx => ⟨hFG hx, (hF.subset hx).2⟩
      have hlarge : G ∩ {x | g x ≤ 0} ⊆ P ∩ {x | g x ≤ 0} :=
        inter_subset_inter_left _ hG.subset
      have hlow := Submodule.finrank_mono (vectorSpan_mono ℝ hinside)
      have hupp := Submodule.finrank_mono
        (vectorSpan_mono ℝ (inter_subset_left : G ∩ {x | g x ≤ 0} ⊆ G))
      exact (hF.mono hlarge hinside).eq_of_finrank_vectorSpan_eq hne (by omega)
  · rintro (rfl | ⟨G, hG, _, rfl⟩)
    · have hz := Mei.Convex.isExposed_setOf_active (fun _ : Unit => g) Finset.univ
      have hzero : IsExposed ℝ {x | g x ≤ 0} {x | g x = 0} := by
        simp only [forall_const, Finset.mem_univ] at hz
        convert hz using 1
        ext x
        exact ⟨fun hx => ⟨hx.le, hx⟩, And.right⟩
      exact (IsExposed.refl P).inter_inter hzero
    · exact hG.inter_inter (IsExposed.refl _)

end TauCeti.IsConvexPolyhedron
