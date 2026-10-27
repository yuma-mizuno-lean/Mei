/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet
public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.LinearAlgebra.Alternating.EdgeFrame

/-!
# A local Stokes formula for intersection indices

Let `σ` be an oriented cell of codimension `k` and `v : Fin (k + 2) → V` an affine test simplex
of dimension `k + 1`. Its boundary is the signed sum `∑ m, (-1) ^ m • (v ∘ m.succAbove)` of its
faces, which are test simplices for `σ`. Suppose that the test meets the facet `F` of `σ` at a
point `p` with positive weight on the vertex `v l`, that face `l` meets `σ` at a point `q ∉ F`,
and that the other faces miss `σ`. Then the intersection index of the test with the signed
boundary facet of `σ` on `F` equals the signed sum of the intersection indices of its faces
with `σ`:
`⟨σ.boundaryFacet F, v⟩ = ∑ m, (-1) ^ m * ⟨σ, v ∘ m.succAbove⟩`.
If the test misses the other facets of `σ`, this is the Stokes formula `⟨dσ, v⟩ = ⟨σ, ∂v⟩` for
the signed facet sum of `σ`. If the test misses `σ`, both sides of that formula vanish.

These are the local comparisons between a small polygonal meridian around a codimension-two
cell and the signed boundary facets of the walls containing it. The signs are computed by the
face formula `AlternatingMap.map_vecCons_sub_faceEdgeFrame` for edge frames and by the outward
contraction `OrientedCell.contract_boundaryFacet` defining boundary orientations. No
boundedness, absence of lineality or nondegeneracy of the test simplex is assumed.
-/

public section

open Module Set

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- **Local Stokes formula at a boundary facet.** Let the test simplex `v` meet the cell `σ` at
a point `∑ j, b j • v j` of its facet `F`, with affine weights `b ≥ 0` positive at `l`, and at a
point `q ∉ F` of its `l`th face, while all other faces miss `σ`. Then its intersection index
with the signed boundary facet on `F` is the signed sum of the intersection indices of its
faces with `σ`. -/
theorem intersectionIndex_boundaryFacet_eq_sum_succAbove (σ : OrientedCell h k) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {v : Fin (k + 2) → V} {b : Fin (k + 2) → ℝ} (hb₀ : ∀ j, 0 ≤ b j) (hb₁ : ∑ j, b j = 1)
    (hpF : ∑ j, b j • v j ∈ F) {l : Fin (k + 2)} (hbl : 0 < b l) {q : V}
    (hql : q ∈ convexHull ℝ (range (v ∘ l.succAbove))) (hqσ : q ∈ σ.carrier) (hqF : q ∉ F)
    (hdisj : ∀ m ≠ l, Disjoint (convexHull ℝ (range (v ∘ m.succAbove))) σ.carrier) :
    (σ.boundaryFacet hF hne hdim).intersectionIndex v =
      ∑ m : Fin (k + 2), (-1) ^ (m : ℕ) * σ.intersectionIndex (v ∘ m.succAbove) := by
  have := h.finiteDimensional
  set p := ∑ j, b j • v j
  set τ := σ.boundaryFacet hF hne hdim
  have hτF : τ.carrier = F := σ.boundaryFacet_carrier hF hne hdim
  -- Only the face through which the segment leaves the test simplex contributes.
  rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ _) fun m _ hm => by
    rw [intersectionIndex_of_disjoint (hdisj m hm), mul_zero]]
  have hpv : p ∈ convexHull ℝ (range v) :=
    (convex_convexHull ℝ _).sum_mem (fun j _ => hb₀ j) hb₁
      fun j _ => subset_convexHull ℝ _ (mem_range_self j)
  rw [intersectionIndex_of_nonempty (σ := τ) ⟨p, hpv, hτF ▸ hpF⟩,
    intersectionIndex_of_nonempty (σ := σ) ⟨q, hql, hqσ⟩]
  -- The vector from `q` to `p` points out of `σ` across `F`.
  let u : vectorSpan ℝ σ.carrier := ⟨p - q, vsub_mem_vectorSpan ℝ (hF.subset hpF) hqσ⟩
  have hu : 0 < (hF.outwardNormal hne hdim).someVector u :=
    (hF.outwardNormal_apply_pos_iff hne hdim hqσ hpF).mpr hqF
  have huF : (u : V) ∉ (affineSpan ℝ τ.carrier).direction := by
    intro hmem
    rw [hτF, direction_affineSpan] at hmem
    have hker : u ∈ (hF.outwardNormal hne hdim).someVector.ker := by
      rw [hF.ker_outwardNormal hne hdim]
      exact hmem
    exact hu.ne' hker
  have hcontract : σ.orientation =
      -τ.orientation.contract τ.isConormal τ.finrank_quotient_direction u huF := by
    rw [σ.contract_boundaryFacet hF hne hdim u huF hu]
    exact (neg_neg σ.orientation).symm
  rw [hcontract, Module.Ray.evalSign_neg, Module.Ray.evalSign_contract]
  -- Compute both signs with one representing form of the facet orientation.
  obtain ⟨α, hα, hτα⟩ : ∃ (α : V [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ) (hα : α ≠ 0),
      τ.orientation = rayOfNeZero ℝ α hα :=
    ⟨_, _, τ.orientation.someVector_ray.symm⟩
  rw [hτα, Module.Ray.evalSign_rayOfNeZero, Module.Ray.evalSign_rayOfNeZero]
  simp only [Function.comp_apply]
  -- Contracting the facet orientation by the inward vector `q - p` gives the face sign.
  have hface := α.map_vecCons_sub_faceEdgeFrame v l hb₁ (convexHull_subset_affineSpan _ hql)
  have hu_eq : (u : V) = -(q - p) := (neg_sub q p).symm
  rw [hu_eq, ← neg_one_smul ℝ (q - p), AlternatingMap.map_vecCons_smul, hface, smul_smul,
    smul_eq_mul]
  simp only [sign_mul, Left.sign_neg, sign_one, sign_pow, sign_pos hbl, mul_one,
    SignType.coe_mul, SignType.coe_neg, SignType.coe_pow, SignType.coe_one]
  have hsq : ((-1 : ℤ) ^ (l : ℕ)) * (-1) ^ (l : ℕ) = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨_, rfl⟩]
  linear_combination (-(SignType.sign (α fun j => v j.succ - v 0) : ℤ)) * hsq

/-- **Stokes formula for a test simplex meeting a single facet.** Under the hypotheses of
`intersectionIndex_boundaryFacet_eq_sum_succAbove`, suppose the test misses the other signed
boundary facets of `σ`. Then its intersection index with the signed facet sum of `σ` equals the
signed sum of the intersection indices of its faces with `σ`. -/
theorem sum_intersectionIndex_boundaryFacets_eq_sum_succAbove (σ : OrientedCell h k)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {v : Fin (k + 2) → V} {b : Fin (k + 2) → ℝ} (hb₀ : ∀ j, 0 ≤ b j) (hb₁ : ∑ j, b j = 1)
    (hpF : ∑ j, b j • v j ∈ F) {l : Fin (k + 2)} (hbl : 0 < b l) {q : V}
    (hql : q ∈ convexHull ℝ (range (v ∘ l.succAbove))) (hqσ : q ∈ σ.carrier) (hqF : q ∉ F)
    (hdisj : ∀ m ≠ l, Disjoint (convexHull ℝ (range (v ∘ m.succAbove))) σ.carrier)
    (hother : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (convexHull ℝ (range v)) τ.carrier) :
    ∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex v =
      ∑ m : Fin (k + 2), (-1) ^ (m : ℕ) * σ.intersectionIndex (v ∘ m.succAbove) := by
  rw [Finset.sum_eq_single_of_mem _ (σ.boundaryFacet_mem_boundaryFacets hF hne hdim)
    fun τ hτ hne' => intersectionIndex_of_disjoint (hother τ hτ fun hτF =>
      hne' (σ.carrier_injOn_boundaryFacets hτ (σ.boundaryFacet_mem_boundaryFacets hF hne hdim)
        (by simpa using hτF)))]
  exact σ.intersectionIndex_boundaryFacet_eq_sum_succAbove hF hne hdim hb₀ hb₁ hpF hbl hql hqσ
    hqF hdisj

/-- **Stokes formula for a test simplex missing the cell.** Both the intersection index with
the signed facet sum and the signed sum over the faces vanish. -/
theorem sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_disjoint
    (σ : OrientedCell h k) {v : Fin (k + 2) → V}
    (hdisj : Disjoint (convexHull ℝ (range v)) σ.carrier) :
    ∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex v =
      ∑ m : Fin (k + 2), (-1) ^ (m : ℕ) * σ.intersectionIndex (v ∘ m.succAbove) := by
  rw [Finset.sum_eq_zero fun τ hτ => intersectionIndex_of_disjoint
      (hdisj.mono_right (σ.carrier_subset_of_mem_boundaryFacets hτ)),
    Finset.sum_eq_zero fun m _ => by
      rw [intersectionIndex_of_disjoint
        (hdisj.mono_left (convexHull_mono (range_comp_subset_range _ _))), mul_zero]]

end Mei.OrientedCell
