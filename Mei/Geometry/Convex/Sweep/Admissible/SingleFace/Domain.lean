/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace

/-!
# Endpoint domains and boundary events of a single face

For one full face `{ν = b}` with singular set `Z` inside it, the endpoint domains of
the two admissible itineraries are explicit. The empty itinerary is admitted exactly
on the open incoming half-space. The one-crossing itinerary is admitted exactly where
the crossing parameter `τ(Q) = (ν Q - b) / ν w` is negative and the crossing point, which
is the `sweepProjection` of `Q` to the face along `w`, misses `Z`.

When `Z` is closed and nowhere dense in the face, the closure of the one-crossing
domain is the whole closed opposite half-space, and its frontier is the union of two
kinds of boundary events: the terminal crossings, where the endpoint lies on the face and
the crossing collapses into it, and the singular shadow of `Z`, where the crossing parameter
is negative and the crossing point lies in `Z`. Every point of either kind is a limit of
admitted endpoints, so no other degeneration occurs. The only boundary event of the incoming
domain is the terminal crossing. A singular set covered by countably many affine subspaces
of ambient codimension at least two has dense complement in the face.

The domains are read off from `nonempty_admissibleRayRealization_iff` and the single-face
classification of `AdmissibleRayRealization`. The decomposition of the boundary of an
endpoint chart into terminal and singular events follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ν : V →L[ℝ] ℝ} {b : ℝ} {u w : V} {Z : Set V}

section Incoming

/-- The empty itinerary is admitted exactly on the open incoming half-space. -/
@[simp]
theorem admissibleBackwardDomain_singleFace_zero (hZ : Z ⊆ {x | ν x = b}) :
    admissibleBackwardDomain (fun _ : Fin 0 => ν) (fun _ => b) (fun _ : Fin 1 => u)
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u} = {x | 0 < (ν x - b) / ν u} :=
  Set.ext fun _ => by
    rw [← nonempty_admissibleRayRealization_iff,
      AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ]
    rfl

end Incoming

section OneCrossing

variable (hnormal : ν w = ν u) (hZ : Z ⊆ {x | ν x = b})

include hnormal hZ

/-- The one-crossing itinerary is admitted exactly where the crossing parameter is negative
and the crossing point misses the singular set. -/
-- Match the single-face pattern before general domain membership unfolds it.
@[simp↓]
theorem mem_admissibleBackwardDomain_singleFace_one_iff {x : V} :
    x ∈ admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u} ↔
      (ν x - b) / ν w < 0 ∧ sweepProjection ν b ((ν w)⁻¹ • w) x ∉ Z := by
  rw [← nonempty_admissibleRayRealization_iff,
    AdmissibleRayRealization.nonempty_singleFace_one_iff hnormal hZ,
    sweepProjection_inv_smul_apply]

/-- The one-crossing endpoint domain is open when the singular set is closed. -/
theorem isOpen_admissibleBackwardDomain_singleFace_one (hZc : IsClosed Z) :
    IsOpen (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) := by
  have : admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u} =
      {x | (ν x - b) / ν w < 0} ∩ sweepProjection ν b ((ν w)⁻¹ • w) ⁻¹' Zᶜ :=
    Set.ext fun _ => mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ
  rw [this]
  exact (isOpen_lt ((ν.continuous.sub continuous_const).div_const _) continuous_const).inter
    (hZc.isOpen_compl.preimage (sweepProjection ν b ((ν w)⁻¹ • w)).cont)

/-- If the singular set is nowhere dense in the face, the closure of the one-crossing
endpoint domain is the closed opposite half-space. -/
theorem closure_admissibleBackwardDomain_singleFace_one (hw : ν w ≠ 0)
    (hdense : {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z)) :
    closure (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) = {x | (ν x - b) / ν w ≤ 0} := by
  refine Set.Subset.antisymm (closure_minimal (fun x hx => ?_) (isClosed_le
    ((ν.continuous.sub continuous_const).div_const _) continuous_const)) fun x hx => ?_
  · exact ((mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ).mp hx).1.le
  -- A point of the face, moved a positive distance backward along `w`, is a limit of
  -- admitted endpoints coming from the part of the face outside `Z`.
  have hpush {y : V} (hy : ν y = b) {s : ℝ} (hs : 0 < s) :
      y - s • w ∈ closure (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) := by
    refine map_mem_closure (f := fun y : V => y - s • w) (continuous_id.sub continuous_const)
      (hdense hy) fun y' hy' => ?_
    obtain ⟨hy'H, hy'Z⟩ := hy'
    refine (mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ).mpr ⟨?_, ?_⟩
    · rw [sub_div_sub_smul_eq_neg hw hy'H]
      exact neg_neg_of_pos hs
    · rwa [sweepProjection_inv_smul_sub_smul hw hy'H]
  -- Every point of the closed half-space is such a point, up to a vanishing displacement.
  have hτ : (ν x - b) / ν w ≤ 0 := hx
  set y := sweepProjection ν b ((ν w)⁻¹ • w) x with hy
  have hyH : ν y = b := by
    exact sweepProjection_height ν b (by simp [hw]) x
  have hxy (s : ℝ) : x - s • w = y - (s - (ν x - b) / ν w) • w := by
    rw [hy, sweepProjection_inv_smul_apply]
    module
  have hc : Continuous fun s : ℝ => x - s • w := by fun_prop
  have hlim : Tendsto (fun s : ℝ => x - s • w) (𝓝[>] 0) (𝓝 x) :=
    (hc.tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
  rw [← closure_closure (s := admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u})]
  refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs => ?_)
  rw [hxy s]
  exact hpush hyH (by have : 0 < s := hs; linarith)

/-- The boundary events of the one-crossing endpoint domain are exactly the terminal
crossings, with the endpoint on the face, and the singular shadow, where the crossing
parameter is negative and the crossing point lies in the singular set. -/
theorem frontier_admissibleBackwardDomain_singleFace_one (hw : ν w ≠ 0) (hZc : IsClosed Z)
    (hdense : {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z)) :
    frontier (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) =
      {x | ν x = b} ∪
        {x | (ν x - b) / ν w < 0 ∧ sweepProjection ν b ((ν w)⁻¹ • w) x ∈ Z} := by
  rw [(isOpen_admissibleBackwardDomain_singleFace_one hnormal hZ hZc).frontier_eq,
    closure_admissibleBackwardDomain_singleFace_one hnormal hZ hw hdense]
  ext x
  rw [Set.mem_sdiff, mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ]
  simp only [mem_ofPred_eq, mem_union, not_and, not_not]
  constructor
  · rintro ⟨hle, hn⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inr ⟨hlt, hn hlt⟩
    · exact Or.inl (sub_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right hw))
  · rintro (h | ⟨hlt, hz⟩)
    · have h0 : (ν x - b) / ν w = 0 := by simp [h]
      exact ⟨h0.le, fun hlt => absurd h0 hlt.ne⟩
    · exact ⟨hlt.le, fun _ => hz⟩

omit hZ in
/-- The incoming half-space and the one-crossing domain are disjoint. -/
theorem disjoint_incoming_admissibleBackwardDomain_singleFace_one :
    Disjoint {x | 0 < (ν x - b) / ν u}
      (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  rw [← nonempty_admissibleRayRealization_iff] at hx'
  obtain ⟨r⟩ := hx'
  have hv : ∀ j : Fin 1, ν (![w, u] j.castSucc) = ν (![w, u] j.succ) := by
    intro j
    fin_cases j
    exact hnormal
  have h := r.div_neg_of_encounter_singleFace hv 0
  rw [← hnormal] at hx
  exact absurd h (not_lt.mpr (le_of_lt hx))

/-- Every endpoint is admitted by exactly one of the empty and one-crossing itineraries,
except the excluded endpoints on the face and those with negative crossing parameter whose
crossing point lies in the singular set. These excluded endpoints form the frontier under the
hypotheses of `frontier_admissibleBackwardDomain_singleFace_one`. -/
theorem incoming_union_admissibleBackwardDomain_singleFace_one (hw : ν w ≠ 0) :
    {x | 0 < (ν x - b) / ν u} ∪ (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) =
      ({x | ν x = b} ∪
        {x | (ν x - b) / ν w < 0 ∧ sweepProjection ν b ((ν w)⁻¹ • w) x ∈ Z})ᶜ := by
  ext x
  rw [mem_union, mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ, ← hnormal]
  simp only [mem_ofPred_eq, mem_compl_iff, mem_union, not_or, not_and]
  have hτ : (ν x - b) / ν w = 0 ↔ ν x = b := by simp [div_eq_zero_iff, hw, sub_eq_zero]
  rcases lt_trichotomy ((ν x - b) / ν w) 0 with h | h | h
  · simp [h, not_lt.mpr h.le, hτ.not.mp h.ne]
  · simp [hτ.mp h]
  · simp [h, not_lt.mpr h.le, hτ.not.mp h.ne']

end OneCrossing

end Mei.Convex
