/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Transverse.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Prism
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.SideFacet
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Map

/-!
# The boundary formula for a transverse swept cell

The signed facets of a negative-ray prism consist of the reversed base and the
reversed sweeps of its signed boundary facets. Summing them gives
`d(Sₙσ) + Sₙ(dσ) = -σ`, with values in polyhedral cochains. The sweep on the
boundary is the linear map on the transverse submodule, rather than a new operation
on presentations. Every boundary facet is transverse because its direction is
contained in the base direction.

This is the generator identity for the sweep homotopy used to cancel closed
polyhedral obstructions. The coboundary here is `OrientedCell.cellCoboundary`;
descent of the source coboundary through subdivision is a separate statement.
The argument assembles `Convex.isExposed_sweep_codimension_one_iff`,
`OrientedCell.boundaryFacet_sweep_base` and `OrientedCell.boundaryFacet_sweep_side`.
Unbounded cells and lineality are allowed.
-/

public section

noncomputable section

namespace Mei.OrientedCell

open Module

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

open Classical in
/-- The signed boundary of a transverse prism consists of its reversed base and
the reversed sweeps of all signed base facets. -/
theorem boundaryFacets_sweep (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).boundaryFacets = insert σ.reverse
      (σ.boundaryFacets.attach.image fun τ =>
        (τ.val.sweep n (σ.notMem_direction_of_mem_boundaryFacets τ.property hn)).reverse) := by
  classical
  have := h.finiteDimensional
  have hnP : i n ∉ vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using hn
  ext τ
  constructor
  · intro hτ
    obtain ⟨G, hG, hne, hdim, rfl⟩ := ((σ.sweep n hn).mem_boundaryFacets τ).mp hτ
    have hclass := (Convex.isExposed_sweep_codimension_one_iff σ.nonempty hnP hne).mp
      ⟨by simpa only [sweep_carrier] using hG,
        by rw [σ.sweep_carrier n hn] at hdim; exact hdim⟩
    rcases hclass with rfl | ⟨F, hFne, hF, hdimF, rfl⟩
    · exact Finset.mem_insert.mpr (Or.inl (σ.boundaryFacet_sweep_base n hn))
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨⟨σ.boundaryFacet hF hFne hdimF,
        σ.boundaryFacet_mem_boundaryFacets hF hFne hdimF⟩, Finset.mem_attach _ _,
        (σ.boundaryFacet_sweep_side n hn hF hFne hdimF).symm⟩
  · intro hτ
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · rw [← σ.boundaryFacet_sweep_base n hn]
      exact (σ.sweep n hn).boundaryFacet_mem_boundaryFacets _ _ _
    · obtain ⟨υ, _, rfl⟩ := Finset.mem_image.mp hτ
      obtain ⟨F, hF, hne, hdim, he⟩ := (σ.mem_boundaryFacets υ.val).mp υ.property
      have hnF : i n ∉ vectorSpan ℝ F := fun hm => hnP (vectorSpan_mono ℝ hF.subset hm)
      have hGF : IsExposed ℝ (σ.sweep n hn).carrier (Convex.sweep F (i n)) := by
        simpa only [sweep_carrier] using hF.sweep_of_transverse hnP
      have hdGF : finrank ℝ (vectorSpan ℝ (Convex.sweep F (i n))) + 1 =
          finrank ℝ (vectorSpan ℝ (σ.sweep n hn).carrier) := by
        rw [sweep_carrier, Convex.finrank_sweep hne hnF,
          Convex.finrank_sweep σ.nonempty hnP, hdim]
      have hmem := (σ.sweep n hn).boundaryFacet_mem_boundaryFacets hGF
        (Convex.sweep_nonempty hne (i n)) hdGF
      rw [σ.boundaryFacet_sweep_side n hn hF hne hdim] at hmem
      simpa only [he] using hmem

private theorem swept_boundaryFacets_injective (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    Function.Injective (fun τ : σ.boundaryFacets =>
      (τ.val.sweep n (σ.notMem_direction_of_mem_boundaryFacets τ.property hn)).reverse) := by
  intro τ υ he
  apply Subtype.ext
  apply σ.carrier_injOn_boundaryFacets τ.property υ.property
  exact (Convex.sweep_eq_sweep_iff_of_subset
    (by simpa only [direction_affineSpan] using hn)
    (σ.carrier_subset_of_mem_boundaryFacets τ.property)
    (σ.carrier_subset_of_mem_boundaryFacets υ.property)).mp
      (by simpa only [reverse_carrier, sweep_carrier] using congrArg carrier he)

open Classical in
private theorem reverse_notMem_swept_boundaryFacets (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    σ.reverse ∉ σ.boundaryFacets.attach.image (fun τ =>
      (τ.val.sweep n (σ.notMem_direction_of_mem_boundaryFacets τ.property hn)).reverse) := by
  classical
  have := h.finiteDimensional
  rintro hmem
  obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hmem
  have hc : Convex.sweep τ.val.carrier (i n) = σ.carrier := by
    simpa only [reverse_carrier, sweep_carrier] using congrArg carrier he
  have hd := Convex.vectorSpan_sweep τ.val.nonempty (i n)
  rw [hc] at hd
  apply hn
  rw [direction_affineSpan, hd]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self (i n))

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The cochain sweep of the signed boundary is the sum of the swept signed facets. -/
theorem sweep_cellCoboundary (σ : OrientedCell h k) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    PolyhedralCochain.sweep n
        ⟨σ.cellCoboundary (R := R) c, σ.cellCoboundary_mem_transverseSubmodule (i n) hn c⟩ =
      ∑ τ : σ.boundaryFacets,
        PolyhedralCochain.mk (τ.val.sweep n
          (σ.notMem_direction_of_mem_boundaryFacets τ.property hn)) c := by
  classical
  have he : (⟨σ.cellCoboundary (R := R) c,
        σ.cellCoboundary_mem_transverseSubmodule (i n) hn c⟩ :
      PolyhedralCochain.transverseSubmodule (i n)) =
      ∑ τ : σ.boundaryFacets, ⟨PolyhedralCochain.mk τ.val c,
        PolyhedralCochain.mk_mem_transverseSubmodule (i n) τ.val
          (σ.notMem_direction_of_mem_boundaryFacets τ.property hn) c⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, cellCoboundary_apply]
    exact (Finset.sum_attach σ.boundaryFacets _).symm
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  exact PolyhedralCochain.sweep_mk n τ.val _ c

/-- The generator sweep homotopy formula, with the boundary swept by the actual
linear map on transverse cochains. -/
theorem cellCoboundary_sweep_add_sweep_cellCoboundary (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    (σ.sweep n hn).cellCoboundary (R := R) c +
        PolyhedralCochain.sweep n ⟨σ.cellCoboundary c,
          σ.cellCoboundary_mem_transverseSubmodule (i n) hn c⟩ =
      -PolyhedralCochain.mk σ c := by
  classical
  rw [cellCoboundary_apply, boundaryFacets_sweep,
    Finset.sum_insert (σ.reverse_notMem_swept_boundaryFacets n hn),
    Finset.sum_image (fun _ _ _ _ he => σ.swept_boundaryFacets_injective n hn he)]
  rw [σ.sweep_cellCoboundary n hn c]
  simp only [PolyhedralCochain.mk_reverse, Finset.sum_neg_distrib, Finset.univ_eq_attach]
  abel

end Mei.OrientedCell

namespace Mei.PolyhedralCochain

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- The sweep homotopy formula for a finite indexed transverse presentation.
The swept boundary is computed in the transverse submodule; repeated cells keep
their indices and contribute with their original coefficients. -/
theorem coboundaryOfFinsupp_sum_sweep_add_sweep_sum_cellCoboundary [Fintype ι]
    (n : N) (σ : ι → OrientedCell h (k + 1))
    (hn : ∀ j, i n ∉ (affineSpan ℝ (σ j).carrier).direction) (c : ι → E) :
    coboundaryOfFinsupp (R := R) (∑ j, Finsupp.single ((σ j).sweep n (hn j)) (c j)) +
      sweep n (∑ j, (⟨(σ j).cellCoboundary (R := R) (c j),
        (σ j).cellCoboundary_mem_transverseSubmodule (i n) (hn j) (c j)⟩ :
        transverseSubmodule (i n))) = -∑ j, mk (σ j) (c j) := by
  classical
  simp only [map_sum, coboundaryOfFinsupp_single]
  rw [← Finset.sum_add_distrib]
  simp only [OrientedCell.cellCoboundary_sweep_add_sweep_cellCoboundary,
    Finset.sum_neg_distrib]

/-- Sweeping a closed finite indexed transverse presentation gives a signed
boundary equal to the negative source cochain. -/
theorem coboundaryOfFinsupp_sum_sweep_of_coboundary_eq_zero [Fintype ι]
    (n : N) (σ : ι → OrientedCell h (k + 1))
    (hn : ∀ j, i n ∉ (affineSpan ℝ (σ j).carrier).direction) (c : ι → E)
    (hclosed : coboundaryOfFinsupp (R := R) (∑ j, Finsupp.single (σ j) (c j)) = 0) :
    coboundaryOfFinsupp (R := R) (∑ j, Finsupp.single ((σ j).sweep n (hn j)) (c j)) =
      -∑ j, mk (σ j) (c j) := by
  classical
  let ζ : transverseSubmodule (R := R) (h := h) (E := E) (k := k + 2) (i n) :=
    ∑ j, ⟨(σ j).cellCoboundary (c j),
      (σ j).cellCoboundary_mem_transverseSubmodule (i n) (hn j) (c j)⟩
  have hboundary : ζ = 0 := by
    apply Subtype.ext
    simpa only [ζ, Submodule.coe_sum, ZeroMemClass.coe_zero, map_sum,
      coboundaryOfFinsupp_single] using hclosed
  have hsum :
      coboundaryOfFinsupp (R := R) (∑ j, Finsupp.single ((σ j).sweep n (hn j)) (c j)) +
        sweep n ζ = -∑ j, mk (σ j) (c j) :=
    coboundaryOfFinsupp_sum_sweep_add_sweep_sum_cellCoboundary n σ hn c
  rw [hboundary, map_zero, add_zero] at hsum
  exact hsum

end Mei.PolyhedralCochain
