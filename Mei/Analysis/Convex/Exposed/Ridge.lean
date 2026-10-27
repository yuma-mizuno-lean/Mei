/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Exposed.Orientation

/-!
# Opposite orientations on a common ridge

Intersecting two exposed facets and taking the induced boundary orientation in
either order gives opposite conormal orientations, whenever their intersection
is a nonempty facet of each. This is the local sign cancellation in the square
of the polyhedral coboundary. The number of facets incident to a ridge is a
separate geometric question.

The argument uses `IsExposed.contract_facetOrientation` and
`Module.Ray.contract_contract`: vectors from each facet towards their
intersection are outward for the other facet, and their contractions
anticommute. Neither convexity nor polyhedrality is needed for this orientation
comparison.
-/

public section

noncomputable section

open Module Set

namespace IsExposed

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [ContinuousAdd K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V] [FiniteDimensional K V] {P F G : Set V} {k : ℕ}

/-- The boundary orientations on a common nonempty ridge, induced through its
two parent exposed facets, are opposite. The parent need not be convex. -/
theorem facetOrientation_inter_eq_neg (hF : IsExposed K P F) (hG : IsExposed K P G)
    (hne : (F ∩ G).Nonempty)
    (hFdim : finrank K (vectorSpan K F) + 1 = finrank K (vectorSpan K P))
    (hGdim : finrank K (vectorSpan K G) + 1 = finrank K (vectorSpan K P))
    (hRdim : finrank K (vectorSpan K (F ∩ G)) + 1 = finrank K (vectorSpan K F))
    (o : Module.Ray K (V [⋀^Fin k]→ₗ[K] K)) (ho : o.IsConormal (vectorSpan K P))
    (hk : finrank K (V ⧸ vectorSpan K P) = k) :
    let hRF := (hF.inter hG).mono hF.subset inter_subset_left
    let hRG := (hF.inter hG).mono hG.subset inter_subset_right
    hRF.facetOrientation hne hRdim (hF.facetOrientation (hne.mono inter_subset_left) hFdim o ho)
        (hF.isConormal_facetOrientation _ hFdim o ho) =
      -hRG.facetOrientation hne (by omega)
        (hG.facetOrientation (hne.mono inter_subset_right) hGdim o ho)
        (hG.isConormal_facetOrientation _ hGdim o ho) := by
  dsimp only
  let hRF := (hF.inter hG).mono hF.subset inter_subset_left
  let hRG := (hF.inter hG).mono hG.subset inter_subset_right
  have hRGdim : finrank K (vectorSpan K (F ∩ G)) + 1 = finrank K (vectorSpan K G) := by
    omega
  have hFn := hne.mono inter_subset_left
  have hGn := hne.mono inter_subset_right
  -- Choose one vector along each facet, pointing outward towards the common ridge.
  obtain ⟨z, hzF, hzG⟩ := hne
  have hproperF : F ∩ G ≠ F := by intro he; rw [he] at hRdim; omega
  have hproperG : F ∩ G ≠ G := by intro he; rw [he] at hRGdim; omega
  obtain ⟨x, hxF, hxR⟩ := exists_of_ssubset (lt_of_le_of_ne inter_subset_left hproperF)
  obtain ⟨y, hyG, hyR⟩ := exists_of_ssubset (lt_of_le_of_ne inter_subset_right hproperG)
  let v : V := z - x
  let w : V := z - y
  have hvF : v ∈ vectorSpan K F := vsub_mem_vectorSpan K hzF hxF
  have hwG : w ∈ vectorSpan K G := vsub_mem_vectorSpan K hzG hyG
  have hvP := vectorSpan_mono K hF.subset hvF
  have hwP := vectorSpan_mono K hG.subset hwG
  have hvpos : 0 < (hRF.outwardNormal ⟨z, hzF, hzG⟩ hRdim).someVector ⟨v, hvF⟩ :=
    (hRF.outwardNormal_apply_pos_iff _ _ hxF ⟨hzF, hzG⟩).mpr hxR
  have hwpos : 0 < (hRG.outwardNormal ⟨z, hzF, hzG⟩ hRGdim).someVector ⟨w, hwG⟩ :=
    (hRG.outwardNormal_apply_pos_iff _ _ hyG ⟨hzF, hzG⟩).mpr hyR
  have hvGpos : 0 < (hG.outwardNormal hGn hGdim).someVector ⟨v, hvP⟩ :=
    (hG.outwardNormal_apply_pos_iff _ _ (hF.subset hxF) hzG).mpr
      (fun hxG => hxR ⟨hxF, hxG⟩)
  have hwFpos : 0 < (hF.outwardNormal hFn hFdim).someVector ⟨w, hwP⟩ :=
    (hF.outwardNormal_apply_pos_iff _ _ (hG.subset hyG) hzF).mpr
      (fun hyF => hyR ⟨hyF, hyG⟩)
  have hvG : v ∉ vectorSpan K G := by
    intro hv
    have hz : (hG.outwardNormal hGn hGdim).someVector ⟨v, hvP⟩ = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_outwardNormal]
      exact hv
    exact (ne_of_gt hvGpos) hz
  have hwF : w ∉ vectorSpan K F := by
    intro hw
    have hz : (hF.outwardNormal hFn hFdim).someVector ⟨w, hwP⟩ = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_outwardNormal]
      exact hw
    exact (ne_of_gt hwFpos) hz
  -- These tangent vectors complement the ridge direction inside the two facets.
  let W := vectorSpan K (F ∩ G)
  have hvW : v ∉ W := fun hv => hvG (vectorSpan_mono K inter_subset_right hv)
  have hwW : w ∉ W := fun hw => hwF (vectorSpan_mono K inter_subset_left hw)
  have hWv : W ⊔ K ∙ v = vectorSpan K F := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le (vectorSpan_mono K inter_subset_left)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hvF)
    · rw [Submodule.finrank_sup_span_singleton hvW]
      exact hRdim
  have hWw : W ⊔ K ∙ w = vectorSpan K G := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le (vectorSpan_mono K inter_subset_right)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hwG)
    · rw [Submodule.finrank_sup_span_singleton hwW]
      exact hRGdim
  have hkF : finrank K (V ⧸ vectorSpan K F) = k + 1 := by
    have := Submodule.finrank_quotient_add_finrank (vectorSpan K F)
    have := Submodule.finrank_quotient_add_finrank (vectorSpan K P)
    omega
  have hkG : finrank K (V ⧸ vectorSpan K G) = k + 1 := by
    have := Submodule.finrank_quotient_add_finrank (vectorSpan K G)
    have := Submodule.finrank_quotient_add_finrank (vectorSpan K P)
    omega
  have hkW : finrank K (V ⧸ W) = k + 2 := by
    have := Submodule.finrank_quotient_add_finrank W
    have := Submodule.finrank_quotient_add_finrank (vectorSpan K F)
    dsimp only [W] at *
    omega
  -- Compute both orders of outward contraction using the boundary characterization.
  let a := hF.facetOrientation hFn hFdim o ho
  let b := hG.facetOrientation hGn hGdim o ho
  have ha : a.IsConormal (vectorSpan K F) := hF.isConormal_facetOrientation _ _ _ _
  have hb : b.IsConormal (vectorSpan K G) := hG.isConormal_facetOrientation _ _ _ _
  let r := hRF.facetOrientation ⟨z, hzF, hzG⟩ hRdim a ha
  let s := hRG.facetOrientation ⟨z, hzF, hzG⟩ hRGdim b hb
  have hr : r.IsConormal W := hRF.isConormal_facetOrientation _ _ _ _
  have hs : s.IsConormal W := hRG.isConormal_facetOrientation _ _ _ _
  have hrv : r.contract hr hkW v hvW = -a :=
    hRF.contract_facetOrientation _ _ a ha hkW ⟨v, hvF⟩ hvpos
  have hsw : s.contract hs hkW w hwW = -b :=
    hRG.contract_facetOrientation _ _ b hb hkW ⟨w, hwG⟩ hwpos
  have haw : a.contract ha hkF w hwF = -o :=
    hF.contract_facetOrientation _ _ o ho hkF ⟨w, hwP⟩ hwFpos
  have hbv : b.contract hb hkG v hvG = -o :=
    hG.contract_facetOrientation _ _ o ho hkG ⟨v, hvP⟩ hvGpos
  have hkv : finrank K (V ⧸ (W ⊔ K ∙ v)) = k + 1 := hWv ▸ hkF
  have hkw : finrank K (V ⧸ (W ⊔ K ∙ w)) = k + 1 := hWw ▸ hkG
  have hwv : w ∉ W ⊔ K ∙ v := hWv ▸ hwF
  have hvw : v ∉ W ⊔ K ∙ w := hWw ▸ hvG
  have hrvw : (r.contract hr hkW v hvW).contract
      (r.isConormal_contract hr hkW v hvW) hkv w hwv = o := by
    rw [Module.Ray.contract_congr _ (-a) _ (Module.Ray.isConormal_neg_iff.mpr ha)
      hkv hkF w hwv hwF hrv, Module.Ray.contract_neg a ha hkF w hwF, haw]
    exact neg_neg o
  have hswv : (s.contract hs hkW w hwW).contract
      (s.isConormal_contract hs hkW w hwW) hkw v hvw = o := by
    rw [Module.Ray.contract_congr _ (-b) _ (Module.Ray.isConormal_neg_iff.mpr hb)
      hkw hkG v hvw hvG hsw, Module.Ray.contract_neg b hb hkG v hvG, hbv]
    exact neg_neg o
  -- Anticommutativity supplies the sign; two injective contractions detect equality.
  have hrwv := r.contract_contract hr hkW v w hvW hwW hkv hkw hwv hvw
  rw [hrvw] at hrwv
  have he : r.contract hr hkW w hwW = -(s.contract hs hkW w hwW) := by
    apply (Module.Ray.contract_eq_contract_iff _ _
      (r.isConormal_contract hr hkW w hwW)
      (Module.Ray.isConormal_neg_iff.mpr (s.isConormal_contract hs hkW w hwW))
      hkw v hvw).mp
    rw [Module.Ray.contract_neg _ (s.isConormal_contract hs hkW w hwW) hkw v hvw, hswv]
    exact (neg_neg ((r.contract hr hkW w hwW).contract
      (r.isConormal_contract hr hkW w hwW) hkw v hvw)).symm.trans
        (congrArg (fun t : Module.Ray K (V [⋀^Fin k]→ₗ[K] K) => -t) hrwv.symm)
  have he' : r = -s := by
    apply (Module.Ray.contract_eq_contract_iff _ _ hr
      (Module.Ray.isConormal_neg_iff.mpr hs) hkW w hwW).mp
    rw [Module.Ray.contract_neg s hs hkW w hwW]
    exact he
  exact he'

end IsExposed
