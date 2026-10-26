/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep
public import Mei.Geometry.Convex.Sweep.Face

/-!
# The oriented base of a transverse prism

The base facet of a negative-ray sweep carries the opposite of the original
cell's orientation. The positive sweeping vector points outwards at the base,
and contracting the original cell's orientation by this vector recovers the
sweep orientation. Contracting the signed base facet's orientation instead
gives the negative sweep orientation, so the boundary convention forces
reversal of the base.
This identifies the base term in the polyhedral sweep boundary formula.

The proof combines `OrientedCell.eq_boundaryFacet_iff` with the unsigned
exposed-face theorem `IsExposed.in_sweep_of_transverse` and the conormal
contraction defining `OrientedCell.sweep`.
-/

public section

noncomputable section

namespace Mei.OrientedCell

open Module

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- The original cell is an exposed subset of its transverse sweep. -/
theorem isExposed_sweep_base (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    IsExposed ℝ (σ.sweep n hn).carrier σ.carrier := by
  have := h.finiteDimensional
  rw [sweep_carrier]
  exact (IsExposed.refl σ.carrier).in_sweep_of_transverse
    (by simpa only [direction_affineSpan] using hn)

/-- The original cell has codimension one in its transverse sweep. -/
theorem finrank_vectorSpan_sweep_base (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    finrank ℝ (vectorSpan ℝ σ.carrier) + 1 =
      finrank ℝ (vectorSpan ℝ (σ.sweep n hn).carrier) := by
  have := h.finiteDimensional
  rw [sweep_carrier, Convex.finrank_sweep σ.nonempty
    (by simpa only [direction_affineSpan] using hn)]

/-- The signed base facet of a transverse negative-ray sweep is the original
cell with reversed orientation. Exposure and codimension are derived from
transversality; no exposing inequality is part of the input. -/
@[simp]
theorem boundaryFacet_sweep_base (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).boundaryFacet (isExposed_sweep_base σ n hn) σ.nonempty
        (finrank_vectorSpan_sweep_base σ n hn) = σ.reverse := by
  have := h.finiteDimensional
  have hF := isExposed_sweep_base σ n hn
  have hdim := finrank_vectorSpan_sweep_base σ n hn
  have hn' : i n ∉ vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using hn
  have hmem : i n ∈ vectorSpan ℝ (σ.sweep n hn).carrier := by
    rw [sweep_carrier, Convex.vectorSpan_sweep σ.nonempty]
    exact (le_sup_right : Submodule.span ℝ {i n} ≤
      vectorSpan ℝ σ.carrier ⊔ Submodule.span ℝ {i n})
        (Submodule.mem_span_singleton_self (i n))
  obtain ⟨x, hx⟩ := σ.nonempty
  have hxsub : x - i n ∈ (σ.sweep n hn).carrier := by
    rw [sweep_carrier]
    exact Convex.mem_sweep_iff_exists.mpr ⟨x, hx, 1, zero_le_one, by simp⟩
  have hxnot : x - i n ∉ σ.carrier := by
    intro hmem
    exact hn' (by simpa using vsub_mem_vectorSpan ℝ hx hmem)
  have hpos : 0 < (hF.outwardNormal σ.nonempty hdim).someVector ⟨i n, hmem⟩ := by
    simpa using (hF.outwardNormal_apply_pos_iff σ.nonempty hdim hxsub hx).mpr hxnot
  symm
  apply ((σ.sweep n hn).eq_boundaryFacet_iff hF σ.nonempty hdim σ.reverse
    (by simp) ⟨i n, hmem⟩ (by simpa using hn) hpos).mpr
  simp only [reverse_orientation, reverse_carrier, sweep_orientation]
  exact Module.Ray.contract_neg σ.orientation σ.isConormal
    σ.finrank_quotient_direction (i n) hn

end Mei.OrientedCell
