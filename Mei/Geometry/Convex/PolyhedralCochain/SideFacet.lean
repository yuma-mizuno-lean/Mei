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
# Signed side facets of a transverse sweep

The side facet swept from a boundary facet has the opposite of its swept boundary
orientation. This is the side term in the boundary formula for a negative-ray prism.
The sign comes from anticommuting the outward and sweeping contractions.

The proof combines `OrientedCell.eq_boundaryFacet_iff`, the unsigned exposed-face
construction `IsExposed.sweep_of_transverse`, and `Module.Ray.contract_contract`.
It allows unbounded cells and lineality, and uses no choice of inequalities.
-/

public section

noncomputable section

open Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- A swept side facet has the reverse of the sweep of its signed base facet. -/
@[simp]
theorem boundaryFacet_sweep_side (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    letI := h.finiteDimensional
    let hnP : i n ∉ vectorSpan ℝ σ.carrier := by
      simpa only [direction_affineSpan] using hn
    let hnF : i n ∉ vectorSpan ℝ F := fun hm => hnP (vectorSpan_mono ℝ hF.subset hm)
    (σ.sweep n hn).boundaryFacet
        (by simpa only [sweep_carrier] using hF.sweep_of_transverse hnP)
        (Convex.sweep_nonempty hne (i n))
        (by rw [sweep_carrier, Convex.finrank_sweep hne hnF,
              Convex.finrank_sweep σ.nonempty hnP, hdim]) =
      ((σ.boundaryFacet hF hne hdim).sweep n
        (by simpa only [boundaryFacet_carrier, direction_affineSpan] using hnF)).reverse := by
  have := h.finiteDimensional
  dsimp only
  have hnP : i n ∉ vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using hn
  have hnF : i n ∉ vectorSpan ℝ F := fun hm => hnP (vectorSpan_mono ℝ hF.subset hm)
  let τ := σ.boundaryFacet hF hne hdim
  have hτcar : τ.carrier = F := σ.boundaryFacet_carrier hF hne hdim
  have hnτ : i n ∉ (affineSpan ℝ τ.carrier).direction := by
    simpa only [hτcar, direction_affineSpan] using hnF
  let υ := (τ.sweep n hnτ).reverse
  have hc : υ.carrier = Convex.sweep F (i n) := by simp [υ, τ]
  have hG : IsExposed ℝ (σ.sweep n hn).carrier (Convex.sweep F (i n)) := by
    simpa only [sweep_carrier] using hF.sweep_of_transverse hnP
  have hdimG : finrank ℝ (vectorSpan ℝ (Convex.sweep F (i n))) + 1 =
      finrank ℝ (vectorSpan ℝ (σ.sweep n hn).carrier) := by
    rw [sweep_carrier, Convex.finrank_sweep hne hnF,
      Convex.finrank_sweep σ.nonempty hnP, hdim]
  -- Use an actual vector from the parent towards its facet; it is outward in both prisms.
  have hproper : F ≠ σ.carrier := by
    intro he
    rw [he] at hdim
    omega
  obtain ⟨x, hx, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  let y := hne.choose
  have hy : y ∈ F := hne.choose_spec
  let v : vectorSpan ℝ σ.carrier :=
    ⟨y - x, vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩
  have hvpos : 0 < (hF.outwardNormal hne hdim).someVector v :=
    (hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF
  have hxG : x ∉ Convex.sweep F (i n) := by
    intro hmem
    obtain ⟨z, hz, t, ht, he⟩ := Convex.mem_sweep_iff_exists.mp hmem
    have hcoords := Convex.sweep_coordinates_unique hnP hx (hF.subset hz)
      (t := 0) (t' := t) (by simpa using he)
    exact hxF (hcoords.1 ▸ hz)
  let v' : vectorSpan ℝ (σ.sweep n hn).carrier :=
    ⟨v, by
      rw [sweep_carrier]
      exact vectorSpan_mono ℝ (Convex.subset_sweep σ.carrier (i n)) v.property⟩
  have hvpos' : 0 < (hG.outwardNormal (Convex.sweep_nonempty hne (i n)) hdimG).someVector v' :=
    (hG.outwardNormal_apply_pos_iff _ _
      (by simpa only [sweep_carrier] using Convex.subset_sweep σ.carrier (i n) hx)
      (Convex.subset_sweep F (i n) hy)).mpr hxG
  have hvG : (v : V) ∉ vectorSpan ℝ (Convex.sweep F (i n)) := by
    intro hm
    have hz : (hG.outwardNormal (Convex.sweep_nonempty hne (i n)) hdimG).someVector v' = 0 := by
      apply LinearMap.mem_ker.mp
      rw [IsExposed.ker_outwardNormal]
      exact hm
    exact (ne_of_gt hvpos') hz
  have hvτ : (v : V) ∉ (affineSpan ℝ τ.carrier).direction := by
    intro hm
    apply hvG
    exact vectorSpan_mono ℝ (Convex.subset_sweep F (i n))
      (by simpa only [hτcar, direction_affineSpan] using hm)
  have hdir : (affineSpan ℝ τ.carrier).direction ⊔ ℝ ∙ (v : V) =
      (affineSpan ℝ σ.carrier).direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply sup_le
      · simpa only [hτcar, direction_affineSpan] using
          vectorSpan_mono ℝ hF.subset
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (by
          simpa only [direction_affineSpan] using v.property)
    · rw [Submodule.finrank_sup_span_singleton hvτ]
      rw [direction_affineSpan, hτcar, direction_affineSpan]
      exact hdim
  have hkn : finrank ℝ (V ⧸ ((affineSpan ℝ τ.carrier).direction ⊔ ℝ ∙ i n)) = k + 1 := by
    have he := (τ.sweep n hnτ).finrank_quotient_direction
    rw [sweep_carrier, direction_affineSpan, Convex.vectorSpan_sweep τ.nonempty] at he
    rw [direction_affineSpan]
    exact he
  have hkm : finrank ℝ (V ⧸ ((affineSpan ℝ τ.carrier).direction ⊔ ℝ ∙ (v : V))) = k + 1 := by
    rw [hdir]
    exact σ.finrank_quotient_direction
  have hvn : (v : V) ∉ (affineSpan ℝ τ.carrier).direction ⊔ ℝ ∙ i n := by
    simpa only [hτcar, direction_affineSpan, ← Convex.vectorSpan_sweep hne] using hvG
  have hnv : i n ∉ (affineSpan ℝ τ.carrier).direction ⊔ ℝ ∙ (v : V) := by
    rwa [hdir]
  have hcontract := τ.orientation.contract_contract τ.isConormal
    τ.finrank_quotient_direction (i n) v hnτ hvτ hkn hkm hvn hnv
  have hboundary := σ.contract_boundaryFacet hF hne hdim v hvτ hvpos
  -- The two contractions exchange order with a minus sign; the boundary already has a minus.
  have hcb := Module.Ray.contract_congr _ (-σ.orientation)
    (τ.orientation.isConormal_contract τ.isConormal τ.finrank_quotient_direction v hvτ)
    (Module.Ray.isConormal_neg_iff.mpr σ.isConormal) hkm σ.finrank_quotient_direction
    (i n) hnv hn hboundary
  have hcb' := hcb.trans (Module.Ray.contract_neg σ.orientation σ.isConormal
    σ.finrank_quotient_direction (i n) hn)
  have hcu := Module.Ray.contract_congr υ.orientation
    (-(τ.orientation.contract τ.isConormal τ.finrank_quotient_direction (i n) hnτ))
    υ.isConormal (Module.Ray.isConormal_neg_iff.mpr
      (τ.orientation.isConormal_contract τ.isConormal τ.finrank_quotient_direction (i n) hnτ))
    υ.finrank_quotient_direction hkn (v : V)
    (by simpa only [hc, direction_affineSpan] using hvG) hvn
    (by simp only [υ, reverse_orientation, sweep_orientation])
  have hneg := Module.Ray.contract_neg
    (τ.orientation.contract τ.isConormal τ.finrank_quotient_direction (i n) hnτ)
    (τ.orientation.isConormal_contract τ.isConormal τ.finrank_quotient_direction (i n) hnτ)
    hkn (v : V) hvn
  have he : υ.orientation.contract υ.isConormal υ.finrank_quotient_direction v'
      (by simpa only [hc, direction_affineSpan] using hvG) = -(σ.sweep n hn).orientation := by
    rw [sweep_orientation]
    exact hcu.trans (hneg.trans ((congrArg Neg.neg hcontract).trans
      ((neg_neg _).trans hcb')))
  exact ((σ.sweep n hn).eq_boundaryFacet_iff hG _ hdimG υ hc v'
    (by simpa only [hc, direction_affineSpan] using hvG) hvpos').mpr he |>.symm

end Mei.OrientedCell
