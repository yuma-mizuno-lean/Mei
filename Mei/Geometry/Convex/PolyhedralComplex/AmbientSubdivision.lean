/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.SignCell.Face
public import Mei.Geometry.Convex.Polyhedron.SignCell.Rational
public import Mathlib.GroupTheory.CosetCover

/-!
# Ambient subdivisions by affine arrangements

The closures of realized sign cells of a finite rational-normal affine
arrangement form a finite polyhedral complex covering the ambient space.
Applying this construction to all defining rows of a finite family of presented
polyhedra expresses every input carrier as a union of cells of one complex.
Redundant and constant rows, empty inputs, unbounded cells and lineality are allowed.
Restricting the rows of an arrangement coarsens its complex, each row hyperplane
is a union of cells, and a linear arrangement has conical cells, with lineality
allowed. A row hyperplane with nonzero linear part is moreover covered by walls:
moving off a point of it in a direction avoiding the other row hyperplanes
through that point reaches a sign cell spanning the hyperplane.

The construction uses the existing realized sign-cell closure family and its
closure under faces. It is therefore extensional in the actual closed cell
carriers rather than retaining duplicate sign assignments as cells.
-/

public section

namespace Mei.FinitePolyhedralComplex

open Mei.Convex Filter Topology

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

/-- A row hyperplane with nonzero linear part is covered by walls: each of its points lies
on a codimension-one cell of the arrangement. -/
theorem exists_mem_ofArrangement_walls_of_eq_zero (g : ι → (V →ᴬ[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toAffineMap.linear) {j : ι}
    (hj : (g j).toAffineMap.linear ≠ 0) {x : V} (hx : g j x = 0) :
    ∃ P ∈ (ofArrangement g hg).walls, x ∈ P := by
  classical
  let := h.finiteDimensional
  let L : ι → V →ₗ[ℝ] ℝ := fun m => (g m).toAffineMap.linear
  have hadd (m : ι) (y v : V) : g m (y + v) = g m y + L m v := by
    simpa [L, vadd_eq_add, add_comm] using (g m).toAffineMap.map_vadd y v
  let K := LinearMap.ker (L j)
  -- A direction in the hyperplane on which every row not vanishing on it is nonzero.
  obtain ⟨w, hw⟩ : ∃ w : K, ∀ m, (∃ v ∈ K, L m v ≠ 0) → L m w ≠ 0 := by
    by_contra! hall
    choose m hm hmw using hall
    obtain ⟨⟨m', hm'⟩, htop⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (k := ℝ) (E := K)
      (p := fun m : {m : ι // ∃ v ∈ K, L m v ≠ 0} => (LinearMap.ker (L m)).comap K.subtype)
      (Set.eq_univ_of_forall fun w => Set.mem_iUnion.mpr ⟨⟨m w, hm w⟩, by simpa using hmw w⟩)
    obtain ⟨v, hvK, hv⟩ := hm'
    have hmem : (⟨v, hvK⟩ : K) ∈ (LinearMap.ker (L m')).comap K.subtype := by
      simp only at htop
      rw [htop]
      trivial
    exact hv (by simpa using hmem)
  have hwj : L j w = 0 := w.property
  -- Points just off `x` in the direction `w` have a constant sign pattern `τ`.
  let τ : ι → SignType := fun m =>
    if g m x = 0 then SignType.sign (L m w) else SignType.sign (g m x)
  have hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), x + r • (w : V) ∈ signCell g τ := by
    have hrow (m : ι) : ∀ᶠ r in 𝓝[>] (0 : ℝ), SignType.sign (g m (x + r • (w : V))) = τ m := by
      by_cases hm : g m x = 0
      · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        simp [τ, hm, hadd, sign_mul, sign_pos hr]
      · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
        have hc : Continuous fun r : ℝ => g m x + r * L m w := by fun_prop
        have hsign := ((continuousAt_sign_of_ne_zero hm).comp_of_eq (hc.continuousAt (x := 0))
          (by simp)).tendsto
        simp only [nhds_discrete, tendsto_pure, Function.comp_def] at hsign
        filter_upwards [hsign] with r hr
        simpa [τ, hm, hadd] using hr
    filter_upwards [Filter.eventually_all.mpr hrow] with r hr
    exact mem_signCell.mpr hr
  have hxP : x ∈ closure (signCell g τ) := by
    refine mem_closure_of_tendsto ?_ hray
    have hc : Continuous fun r : ℝ => x + r • (w : V) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨r₀, hr₀⟩ := hray.exists
  have hτne : (signCell g τ).Nonempty := ⟨_, hr₀⟩
  -- The closed cell spans exactly the hyperplane direction `K`.
  have hdir : (affineSpan ℝ (closure (signCell g τ))).direction = K := by
    apply le_antisymm
    · have hsub : closure (signCell g τ) ⊆ (AffineSubspace.mk' x K : Set V) := by
        intro y hy
        rw [closure_signCell hτne] at hy
        have hτj : τ j = 0 := by simp [τ, hx, hwj]
        have hy0 := (mem_weakSignCell.mp hy j).1 hτj
        rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker]
        have := hadd j x (y - x)
        rw [add_sub_cancel, hy0, hx, zero_add] at this
        exact this.symm
      simpa only [AffineSubspace.direction_mk'] using
        AffineSubspace.direction_le (affineSpan_le.mpr hsub)
    · intro v hv
      have hrow (m : ι) : ∀ᶠ c in 𝓝 (0 : ℝ),
          SignType.sign (g m (x + r₀ • (w : V) + c • v)) = τ m := by
        by_cases hm : g m (x + r₀ • (w : V)) = 0
        · have hτm : τ m = 0 := by rw [← mem_signCell.mp hr₀ m, hm, sign_zero]
          have hLv : L m v = 0 := by
            by_contra hLv
            have hx0 : g m x = 0 := by
              by_contra hx0
              simp [τ, hx0] at hτm
            have hLw : L m w = 0 := by simpa [τ, hx0] using hτm
            exact hw m ⟨v, hv, hLv⟩ hLw
          exact Eventually.of_forall fun c => by
            rw [hadd, hm, map_smul, hLv, smul_zero, add_zero, sign_zero, hτm]
        · have hc : Continuous fun c : ℝ => g m (x + r₀ • (w : V)) + c * L m v := by fun_prop
          have hsign := ((continuousAt_sign_of_ne_zero hm).comp_of_eq
            (hc.continuousAt (x := 0)) (by simp)).tendsto
          simp only [nhds_discrete, tendsto_pure, Function.comp_def] at hsign
          filter_upwards [hsign] with c hc
          rw [← mem_signCell.mp hr₀ m, hadd, map_smul, smul_eq_mul]
          simpa using hc
      obtain ⟨c, hc, hc0⟩ := ((Filter.eventually_all.mpr hrow).filter_mono
        nhdsWithin_le_nhds |>.and self_mem_nhdsWithin : ∀ᶠ c in 𝓝[≠] (0 : ℝ), _).exists
      have hmem := AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (subset_closure (mem_signCell.mpr hc)))
        (subset_affineSpan ℝ _ (subset_closure hr₀))
      rw [vsub_eq_sub, add_sub_cancel_left] at hmem
      exact (Submodule.smul_mem_iff _ hc0).mp hmem
  refine ⟨closure (signCell g τ), (mem_cellsOfCodimension _ 1 _).mpr
    ⟨mem_ofArrangement_cells.mpr ⟨τ, hτne, rfl⟩, ?_⟩, hxP⟩
  rw [hdir]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hj

/-- A linear arrangement has conical cells, with lineality allowed. -/
theorem isConical_ofArrangement (g : ι → (V →L[ℝ] ℝ))
    (hg : ∀ j, Toric.IsRationalFunctional h (g j).toLinearMap) :
    (ofArrangement (fun j => (g j).toContinuousAffineMap) hg).IsConical := by
  apply (isConical_iff _).mpr
  intro P hP
  obtain ⟨σ, hσ, rfl⟩ := mem_ofArrangement_cells.mp hP
  rw [closure_signCell hσ]
  exact ⟨weakSignCellCone g σ, coe_weakSignCellCone g σ⟩

end Mei.FinitePolyhedralComplex
