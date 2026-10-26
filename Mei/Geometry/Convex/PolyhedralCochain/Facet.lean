/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Face
public import Mei.LinearAlgebra.Alternating.Extension
public import Mei.Analysis.Convex.Exposed.Orientation

/-!
# Oriented boundary facets

Every nonempty exposed facet of an oriented rational-normal cell has a canonical
boundary orientation. Contracting it by any outward tangent vector gives the
negative of the parent's conormal orientation. Equivalently, append an outward
conormal to the parent's conormal frame and multiply by `(-1)^(k+1)` for a
parent of codimension `k`. This is the signed generator needed for the
polyhedral coboundary.

The construction uses `IsExposed.outwardNormal` on the parent direction and
Mathlib's `Subspace.dualLift` and `AlternatingMap.alternatizeUncurryFin`.
The contraction characterization proves independence of the outward vector
and determines the oriented facet uniquely. `boundaryFacet_orientation` identifies
it with the general ordered-field construction `IsExposed.facetOrientation`.
No inner product, boundedness,
salience or full-dimensionality is assumed.
-/

public section

open Module

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

private theorem exists_boundaryFacet (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    letI := h.finiteDimensional
    ∃ τ : OrientedCell h (k + 1), τ.carrier = F ∧
      ∀ (v : vectorSpan ℝ σ.carrier)
        (hv : (v : V) ∉ (affineSpan ℝ τ.carrier).direction),
        0 < (hF.outwardNormal hne hdim).someVector v →
        τ.orientation.contract τ.isConormal τ.finrank_quotient_direction v hv =
          -σ.orientation := by
  have := h.finiteDimensional
  -- Extend the canonical outward functional from the parent direction.
  let W := vectorSpan ℝ σ.carrier
  let m := (hF.outwardNormal hne hdim).someVector
  let l := Subspace.dualLift W m
  let β := σ.orientation.someVector
  have hβ : β ∈ W.conormalForms (Fin k) := by
    simpa only [β, W, direction_affineSpan, Module.Ray.isConormal_iff] using σ.isConormal
  let α := -AlternatingMap.alternatizeUncurryFin (l.smulRight β)
  have hα : α ∈ (vectorSpan ℝ F).conormalForms (Fin (k + 1)) := by
    rw [Submodule.mem_conormalForms]
    intro v j hv
    apply neg_eq_zero.mpr
    apply (Submodule.mem_conormalForms.mp
      (Submodule.conormalForms_alternatizeUncurryFin_smulRight hβ l)) v j
    have hvW : v j ∈ W := vectorSpan_mono ℝ hF.subset hv
    refine ⟨hvW, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    dsimp only [l]
    rw [Subspace.dualLift_of_mem hvW]
    apply LinearMap.mem_ker.mp
    rw [IsExposed.ker_outwardNormal]
    exact hv
  -- Contraction recovers the parent form on every outward tangent vector.
  have hcontract (v : W) : α.curryLeft v = m v • (-β) := by
    ext a
    have he := AlternatingMap.congr_fun
      (Submodule.curryLeft_alternatizeUncurryFin_smulRight_of_mem hβ l v.property) a
    simpa only [α, AlternatingMap.curryLeft_apply_apply, neg_apply, smul_apply,
      l, Subspace.dualLift_of_subtype, smul_neg] using congrArg Neg.neg he
  obtain ⟨v, hv⟩ := LinearMap.surjective_iff_ne_zero.mpr
    (hF.outwardNormal hne hdim).someVector_ne_zero 1
  have hα0 : α ≠ 0 := by
    intro hz
    have he := hcontract v
    rw [hz, AlternatingMap.curryLeft_zero, LinearMap.zero_apply, hv] at he
    exact σ.orientation.someVector_ne_zero (by simpa only [one_smul, neg_eq_zero, β] using he.symm)
  -- Package the signed form as a cell with the actual facet support.
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hconv : Convex ℝ σ.carrier := hP ▸ P.convex
  let τ : OrientedCell h (k + 1) :=
    { carrier := F
      rational := hF.isExtreme.isRationalNormalPolyhedron σ.rational
        (hF.convex hconv)
      nonempty := hne
      finrank_direction_add := by
        have hp := σ.finrank_direction_add
        rw [direction_affineSpan] at hp ⊢
        omega
      orientation := rayOfNeZero ℝ α hα0
      isConormal := by
        rw [Module.Ray.isConormal_rayOfNeZero_iff, direction_affineSpan]
        exact hα }
  refine ⟨τ, rfl, fun v hv hpos => ?_⟩
  rw [Module.Ray.contract_rayOfNeZero]
  have he := hcontract v
  rw [← σ.orientation.someVector_ray, neg_rayOfNeZero, ray_eq_iff]
  rw [he]
  exact (SameRay.sameRay_pos_smul_right (-β) hpos).symm

/-- The signed boundary facet of an oriented cell. Its contraction by an outward
tangent vector is the negative of the parent's orientation. -/
def boundaryFacet (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    OrientedCell h (k + 1) :=
  (exists_boundaryFacet σ hF hne hdim).choose

/-- The boundary facet has exactly the prescribed support. -/
@[simp]
theorem boundaryFacet_carrier (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    (σ.boundaryFacet hF hne hdim).carrier = F :=
  (exists_boundaryFacet σ hF hne hdim).choose_spec.1

/-- Every outward tangent vector computes the boundary orientation by contraction;
neither its length nor a particular exposing inequality is part of the result. -/
theorem contract_boundaryFacet (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (v : vectorSpan ℝ σ.carrier)
    (hv : (v : V) ∉ (affineSpan ℝ (σ.boundaryFacet hF hne hdim).carrier).direction) :
    letI := h.finiteDimensional
    0 < (hF.outwardNormal hne hdim).someVector v →
    (σ.boundaryFacet hF hne hdim).orientation.contract
      (σ.boundaryFacet hF hne hdim).isConormal
      (σ.boundaryFacet hF hne hdim).finrank_quotient_direction v hv = -σ.orientation :=
  (exists_boundaryFacet σ hF hne hdim).choose_spec.2 v hv

/-- Among cells with the prescribed support, a single outward contraction
characterizes the signed boundary facet. -/
theorem eq_boundaryFacet_iff (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (τ : OrientedCell h (k + 1)) (hτ : τ.carrier = F)
    (v : vectorSpan ℝ σ.carrier)
    (hv : (v : V) ∉ (affineSpan ℝ τ.carrier).direction) :
    letI := h.finiteDimensional
    0 < (hF.outwardNormal hne hdim).someVector v →
    (τ = σ.boundaryFacet hF hne hdim ↔
      τ.orientation.contract τ.isConormal τ.finrank_quotient_direction v hv =
        -σ.orientation) := by
  have := h.finiteDimensional
  intro hpos
  constructor
  · rintro rfl
    exact σ.contract_boundaryFacet hF hne hdim v hv hpos
  · intro he
    have hc : τ.carrier = (σ.boundaryFacet hF hne hdim).carrier := by simp [hτ]
    have hp : (σ.boundaryFacet hF hne hdim).orientation.IsConormal
        (affineSpan ℝ τ.carrier).direction := by
      rw [hc]
      exact (σ.boundaryFacet hF hne hdim).isConormal
    have he' := σ.contract_boundaryFacet hF hne hdim v (by rwa [← hc]) hpos
    have hq : (σ.boundaryFacet hF hne hdim).orientation.contract hp
        τ.finrank_quotient_direction v hv = -σ.orientation := by
      simpa only [hc] using he'
    have ho := (Module.Ray.contract_eq_contract_iff τ.orientation
      (σ.boundaryFacet hF hne hdim).orientation τ.isConormal hp
      τ.finrank_quotient_direction v hv).mp (he.trans hq.symm)
    exact OrientedCell.ext hc ho

/-- Reversing a cell reverses the signed orientation of each boundary facet. -/
@[simp]
theorem boundaryFacet_reverse (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    σ.reverse.boundaryFacet (by simpa using hF) hne
        (by rw [reverse_carrier]; exact hdim) =
      (σ.boundaryFacet hF hne hdim).reverse := by
  have := h.finiteDimensional
  have hproper : F ≠ σ.carrier := by
    intro heq
    rw [heq] at hdim
    omega
  obtain ⟨x, hx, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  have hnecopy := hne
  obtain ⟨y, hy⟩ := hnecopy
  let v : vectorSpan ℝ σ.carrier :=
    ⟨y - x, vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩
  have hpos : 0 < (hF.outwardNormal hne hdim).someVector v :=
    (hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF
  have hn : (v : V) ∉ (affineSpan ℝ (σ.boundaryFacet hF hne hdim).carrier).direction := by
    intro hmem
    have hz : (hF.outwardNormal hne hdim).someVector v = 0 := by
      apply LinearMap.mem_ker.mp
      rw [IsExposed.ker_outwardNormal]
      simpa only [boundaryFacet_carrier, direction_affineSpan, Submodule.mem_comap,
        Submodule.subtype_apply] using hmem
    linarith
  have he := (Module.Ray.contract_neg (σ.boundaryFacet hF hne hdim).orientation
    (σ.boundaryFacet hF hne hdim).isConormal
    (σ.boundaryFacet hF hne hdim).finrank_quotient_direction v hn).trans
      (congrArg Neg.neg (σ.contract_boundaryFacet hF hne hdim v hn hpos))
  symm
  have hc := σ.reverse.eq_boundaryFacet_iff (by simpa using hF) hne
    (by rw [reverse_carrier]; exact hdim) (σ.boundaryFacet hF hne hdim).reverse (by simp)
    ⟨y - x, by simpa only [reverse_carrier] using v.property⟩ (by simpa using hn)
  have hFr : IsExposed ℝ σ.reverse.carrier F := by simpa only [reverse_carrier] using hF
  have hdr : finrank ℝ (vectorSpan ℝ F) + 1 =
      finrank ℝ (vectorSpan ℝ σ.reverse.carrier) := by rw [reverse_carrier]; exact hdim
  have hpos' := (hFr.outwardNormal_apply_pos_iff hne hdr
    (x := x) (y := y) (by simpa only [reverse_carrier] using hx) hy).mpr hxF
  apply (hc hpos').mpr
  dsimp only [v] at he
  convert he using 1 <;> simp only [reverse_carrier, reverse_orientation]

/-- The boundary facet orientation is the canonical signed covector extension of
its parent's orientation. -/
theorem boundaryFacet_orientation (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    letI := h.finiteDimensional
    (σ.boundaryFacet hF hne hdim).orientation =
      hF.facetOrientation hne hdim σ.orientation
        (by simpa only [direction_affineSpan] using σ.isConormal) := by
  have := h.finiteDimensional
  have ho : σ.orientation.IsConormal (vectorSpan ℝ σ.carrier) := by
    simpa only [direction_affineSpan] using σ.isConormal
  have hp : (σ.boundaryFacet hF hne hdim).orientation.IsConormal (vectorSpan ℝ F) := by
    simpa only [boundaryFacet_carrier, direction_affineSpan] using
      (σ.boundaryFacet hF hne hdim).isConormal
  have hk : finrank ℝ (V ⧸ vectorSpan ℝ F) = k + 1 := by
    have := (vectorSpan ℝ F).finrank_quotient_add_finrank
    have hσ := σ.finrank_direction_add
    rw [direction_affineSpan] at hσ
    omega
  obtain ⟨v, hv⟩ := LinearMap.surjective_iff_ne_zero.mpr
    (hF.outwardNormal hne hdim).someVector_ne_zero 1
  have hpos : 0 < (hF.outwardNormal hne hdim).someVector v := by
    rw [hv]
    exact zero_lt_one
  have hn : (v : V) ∉ (affineSpan ℝ (σ.boundaryFacet hF hne hdim).carrier).direction := by
    intro hmem
    have hz : (hF.outwardNormal hne hdim).someVector v = 0 := by
      apply LinearMap.mem_ker.mp
      rw [IsExposed.ker_outwardNormal]
      simpa only [boundaryFacet_carrier, direction_affineSpan, Submodule.mem_comap,
        Submodule.subtype_apply] using hmem
    exact (ne_of_gt hpos) hz
  symm
  apply (hF.facetOrientation_eq_iff_contract hne hdim σ.orientation ho
    (σ.boundaryFacet hF hne hdim).orientation hp hk v hpos).mpr
  simpa only [boundaryFacet_carrier, direction_affineSpan] using
    σ.contract_boundaryFacet hF hne hdim v hn hpos

end Mei.OrientedCell
