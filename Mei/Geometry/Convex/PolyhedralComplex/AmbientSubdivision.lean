/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Geometry.Convex.Polyhedron.SignCell.Face
public import Mei.Geometry.Convex.Polyhedron.SignCell.Rational

/-!
# Ambient subdivisions by affine arrangements

The closures of realized sign cells of a finite rational-normal affine
arrangement form a finite polyhedral complex covering the ambient space.
Applying this construction to all defining rows of a finite family of presented
polyhedra expresses every input carrier as a union of cells of one complex.
Redundant and constant rows, empty inputs, unbounded cells and lineality are allowed.

The construction uses the existing realized sign-cell closure family and its
closure under faces. It is therefore extensional in the actual closed cell
carriers rather than retaining duplicate sign assignments as cells.
-/

public section

namespace Mei.FinitePolyhedralComplex

open Mei.Convex

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι]

/-- The finite complex of closures of the realized sign cells of a rational-normal
affine arrangement. Its support is the entire ambient space. -/
noncomputable def ofArrangement (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    FinitePolyhedralComplex h where
  cells := (finite_realizedSignCellClosures g).toFinset
  nonempty P hP := nonempty_of_mem_realizedSignCellClosures (by simpa using hP)
  rational P hP := isRationalNormalPolyhedron_of_mem_realizedSignCellClosures hg
    (by simpa using hP)
  face_closed P hP F hF := by
    obtain ⟨hne, hexposed⟩ := isPolyhedralFace_iff.mp hF
    have hPF := hexposed.isExtreme.mem_realizedSignCellClosures (by simpa using hP)
      (hexposed.convex (isConvexPolyhedron_of_mem_realizedSignCellClosures
        (by simpa using hP)).convex) hne
    simpa using hPF
  inter_face P hP Q hQ _ := by
    have hP' : P ∈ realizedSignCellClosures g := by simpa using hP
    have hQ' : Q ∈ realizedSignCellClosures g := by simpa using hQ
    exact (isExtreme_inter_of_mem_realizedSignCellClosures hP' hQ').isExposed_of_isConvexPolyhedron
      (isConvexPolyhedron_of_mem_realizedSignCellClosures hP')
      ((isConvexPolyhedron_of_mem_realizedSignCellClosures hP').convex.inter
        (isConvexPolyhedron_of_mem_realizedSignCellClosures hQ').convex)

/-- The cells are exactly the actual closures of nonempty strict sign cells. -/
@[simp]
theorem mem_ofArrangement_cells {g : ι → (V →ᴬ[ℝ] ℝ)}
    {hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear} {P : Set V} :
    P ∈ (ofArrangement g hg).cells ↔
      ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ) := by
  simp [ofArrangement]

/-- A finite affine arrangement subdivides all of the ambient space. -/
@[simp]
theorem support_ofArrangement (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) :
    (ofArrangement g hg).support = Set.univ := by
  ext x
  simp only [mem_support, mem_ofArrangement_cells]
  simpa only [Set.mem_sUnion, mem_realizedSignCellClosures]
    using Set.ext_iff.mp (sUnion_realizedSignCellClosures g) x

/-- The ambient subdivision obtained from every defining row of a finite family
of presented rational-normal polyhedra. The family may be empty. -/
noncomputable def ambientSubdivision (P : ι → RationalAffinePolyhedron h) :
    FinitePolyhedralComplex h :=
  ofArrangement (fun j : Σ a, Fin (P a).numConstraints => (P j.1).inequality j.2)
    (fun j => (P j.1).rational_linear j.2)

/-- Ambient subdivision cells are closures of realized sign cells of the combined
family of all the input inequalities. -/
@[simp]
theorem mem_ambientSubdivision_cells {P : ι → RationalAffinePolyhedron h} {Q : Set V} :
    Q ∈ (ambientSubdivision P).cells ↔
      ∃ σ, (signCell (fun j : Σ a, Fin (P a).numConstraints =>
        (P j.1).inequality j.2) σ).Nonempty ∧
        Q = closure (signCell (fun j : Σ a, Fin (P a).numConstraints =>
          (P j.1).inequality j.2) σ) := by
  exact mem_ofArrangement_cells

/-- The ambient subdivision covers the entire ambient space, even for empty or
inconsistent input presentations. -/
@[simp]
theorem support_ambientSubdivision (P : ι → RationalAffinePolyhedron h) :
    (ambientSubdivision P).support = Set.univ :=
  support_ofArrangement _ _

/-- Each point of an input polyhedron lies in a subdivision cell entirely
contained in that polyhedron. -/
theorem exists_mem_ambientSubdivision_cells_subset
    (P : ι → RationalAffinePolyhedron h) (a : ι) {x : V} (hx : x ∈ (P a).carrier) :
    ∃ Q ∈ (ambientSubdivision P).cells, x ∈ Q ∧ Q ⊆ (P a).carrier := by
  let g := fun j : Σ a, Fin (P a).numConstraints => (P j.1).inequality j.2
  let σ := fun j => SignType.sign (g j x)
  have hsign : x ∈ signCell g σ := mem_signCell_sign g x
  refine ⟨closure (signCell g σ),
    mem_ambientSubdivision_cells.mpr ⟨σ, ⟨x, hsign⟩, rfl⟩, subset_closure hsign, ?_⟩
  apply closure_minimal ?_ (P a).isClosed
  intro y hy
  apply RationalAffinePolyhedron.mem_carrier.mpr
  intro j
  apply sign_nonpos_iff.mp
  rw [mem_signCell.mp hy ⟨a, j⟩]
  exact sign_nonpos_iff.mpr (RationalAffinePolyhedron.mem_carrier.mp hx j)

/-- Every input carrier is exactly the union of subdivision cells contained in it. -/
theorem carrier_eq_iUnion_ambientSubdivision_cells
    (P : ι → RationalAffinePolyhedron h) (a : ι) :
    (P a).carrier = ⋃ (Q : Set V) (_ : Q ∈ (ambientSubdivision P).cells)
      (_ : Q ⊆ (P a).carrier), Q := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨Q, hQ, hxQ, hsub⟩ := exists_mem_ambientSubdivision_cells_subset P a hx
    exact ⟨Q, hQ, hsub, hxQ⟩
  · rintro ⟨Q, _, hsub, hxQ⟩
    exact hsub hxQ

/-- Restricting the rows of an arrangement coarsens its complex. The row map
need not be injective: repeated inequalities do not change the conclusion. -/
theorem ofArrangement_isSubdivision_comp {κ : Type*} [Finite κ]
    (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) (f : κ → ι) :
    (ofArrangement g hg).IsSubdivision
      (ofArrangement (g ∘ f) (fun j => hg (f j))) := by
  apply isSubdivision_iff.mpr
  refine ⟨?_, by simp⟩
  apply isWeakRefinement_iff.mpr
  intro P hP
  obtain ⟨σ, ⟨x, hx⟩, rfl⟩ := mem_ofArrangement_cells.mp hP
  have hsub : signCell g σ ⊆ signCell (g ∘ f) (σ ∘ f) :=
    fun y hy => mem_signCell.mpr (fun j => mem_signCell.mp hy (f j))
  exact ⟨closure (signCell (g ∘ f) (σ ∘ f)),
    mem_ofArrangement_cells.mpr ⟨σ ∘ f, ⟨x, hsub hx⟩, rfl⟩, closure_mono hsub⟩

/-- Each row hyperplane is a union of cells of the arrangement. -/
theorem zeroLocus_eq_iUnion_ofArrangement_cells (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) (j : ι) :
    {x | g j x = 0} = ⋃ (P : Set V) (_ : P ∈ (ofArrangement g hg).cells)
      (_ : P ⊆ {x | g j x = 0}), P := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hx
    let σ := fun a => SignType.sign (g a x)
    have hσ : x ∈ signCell g σ := mem_signCell_sign g x
    refine ⟨closure (signCell g σ),
      mem_ofArrangement_cells.mpr ⟨σ, ⟨x, hσ⟩, rfl⟩, ?_, subset_closure hσ⟩
    rw [closure_signCell ⟨x, hσ⟩]
    intro y hy
    exact (mem_weakSignCell.mp hy j).1 (by simp [σ, hx])
  · rintro ⟨P, _, hP, hxP⟩
    exact hP hxP

/-- A linear arrangement has conical cells, with lineality allowed. -/
theorem isConical_ofArrangement (g : ι → (V →L[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toLinearMap) :
    (ofArrangement (fun j => (g j).toContinuousAffineMap) hg).IsConical := by
  apply (isConical_iff _).mpr
  intro P hP
  obtain ⟨σ, hσ, rfl⟩ := mem_ofArrangement_cells.mp hP
  rw [closure_signCell hσ]
  refine ⟨{
    carrier := weakSignCell (fun j => (g j).toContinuousAffineMap) σ
    add_mem' := ?_
    zero_mem' := ?_
    smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    rw [mem_weakSignCell] at hx hy ⊢
    intro j
    simp only [ContinuousLinearMap.coe_toContinuousAffineMap, map_add] at hx hy ⊢
    exact ⟨fun hj => by simp [(hx j).1 hj, (hy j).1 hj],
      fun hj => add_nonpos ((hx j).2.1 hj) ((hy j).2.1 hj),
      fun hj => add_nonneg ((hx j).2.2 hj) ((hy j).2.2 hj)⟩
  · simp [mem_weakSignCell]
  · intro c x hx
    rw [mem_weakSignCell] at hx ⊢
    intro j
    simp only [ContinuousLinearMap.coe_toContinuousAffineMap, ← Nonneg.coe_smul,
      map_smul, smul_eq_mul] at hx ⊢
    exact ⟨fun hj => by simp [(hx j).1 hj],
      fun hj => mul_nonpos_of_nonneg_of_nonpos c.property ((hx j).2.1 hj),
      fun hj => mul_nonneg c.property ((hx j).2.2 hj)⟩

end Mei.FinitePolyhedralComplex
