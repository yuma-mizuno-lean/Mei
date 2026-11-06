/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.SingleFace
public import Mei.Geometry.Convex.Sweep.Topology

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
the crossing collapses into it, and the singular shadow of `Z`, where the crossing lands in
`Z`. Every point of either kind is a limit of admitted endpoints, so no other
degeneration occurs. The only boundary event of the incoming domain is the terminal
crossing. A singular set contained in a proper affine subspace of ambient codimension at
least two is nowhere dense in the face.

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

/-- The sweep projection onto a face along a transverse direction moves a point to
its computed crossing with the face. -/
theorem sweepProjection_inv_smul_apply (x : V) :
    sweepProjection ν b ((ν w)⁻¹ • w) x = x - ((ν x - b) / ν w) • w := by
  rw [sweepProjection_apply, smul_smul, div_eq_mul_inv]
  module

/-- Moving a point of the face backward along a transverse direction by `s` makes the
crossing parameter `-s`. -/
theorem sub_div_sub_smul_eq_neg (hw : ν w ≠ 0) {y : V} (hy : ν y = b) (s : ℝ) :
    (ν (y - s • w) - b) / ν w = -s := by
  simp only [map_sub, map_smul, smul_eq_mul, hy]
  field_simp
  ring

/-- Moving a point of the face backward along `w` and projecting returns the point. -/
theorem sweepProjection_inv_smul_sub_smul (hw : ν w ≠ 0) {y : V} (hy : ν y = b) (s : ℝ) :
    sweepProjection ν b ((ν w)⁻¹ • w) (y - s • w) = y := by
  rw [sweepProjection_inv_smul_apply, sub_div_sub_smul_eq_neg hw hy]
  module

section Incoming

/-- The empty itinerary is admitted exactly on the open incoming half-space. -/
theorem admissibleBackwardDomain_singleFace_zero (hZ : Z ⊆ {x | ν x = b}) :
    admissibleBackwardDomain (fun _ : Fin 0 => ν) (fun _ => b) (fun _ : Fin 1 => u)
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u} = {x | 0 < (ν x - b) / ν u} :=
  Set.ext fun _ => by
    rw [← nonempty_admissibleRayRealization_iff,
      AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ]
    rfl

/-- The incoming half-space is open. -/
theorem isOpen_singleFace_incoming : IsOpen {x : V | 0 < (ν x - b) / ν u} :=
  isOpen_lt continuous_const ((ν.continuous.sub continuous_const).div_const _)

/-- The closure of the incoming half-space is the closed half-space. -/
theorem closure_singleFace_incoming (hu : ν u ≠ 0) :
    closure {x : V | 0 < (ν x - b) / ν u} = {x | 0 ≤ (ν x - b) / ν u} := by
  refine Set.Subset.antisymm (closure_minimal (ofPred_subset_ofPred.mpr fun _ h => h.le)
    (isClosed_le continuous_const ((ν.continuous.sub continuous_const).div_const _)))
    fun x hx => ?_
  have hc : Continuous fun s : ℝ => x + s • u := by fun_prop
  have hlim : Tendsto (fun s : ℝ => x + s • u) (𝓝[>] 0) (𝓝 x) :=
    (hc.tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs => ?_)
  have hx' : 0 ≤ (ν x - b) / ν u := hx
  simp only [mem_ofPred_eq, map_add, map_smul, smul_eq_mul, add_sub_right_comm, add_div,
    mul_div_assoc, div_self hu, mul_one]
  exact add_pos_of_nonneg_of_pos hx' hs

/-- The only boundary event of the incoming half-space is the terminal crossing at the face. -/
theorem frontier_singleFace_incoming (hu : ν u ≠ 0) :
    frontier {x : V | 0 < (ν x - b) / ν u} = {x | ν x = b} := by
  rw [isOpen_singleFace_incoming.frontier_eq, closure_singleFace_incoming hu]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_lt]
  constructor
  · rintro ⟨h0, h1⟩
    have := le_antisymm h1 h0
    rw [div_eq_zero_iff] at this
    exact sub_eq_zero.mp (this.resolve_right hu)
  · intro hx
    simp [hx]

end Incoming

section OneCrossing

variable (hnormal : ν w = ν u) (hZ : Z ⊆ {x | ν x = b})

include hnormal hZ

/-- The one-crossing itinerary is admitted exactly where the crossing parameter is negative
and the crossing point misses the singular set. -/
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
    rw [hy, sweepProjection_inv_smul_apply]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
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
point lies in the singular set. -/
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

/-- The incoming half-space and the one-crossing domain are disjoint. -/
theorem disjoint_incoming_admissibleBackwardDomain_singleFace_one :
    Disjoint {x | 0 < (ν x - b) / ν u}
      (admissibleBackwardDomain (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
        (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν u}) := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have h := ((mem_admissibleBackwardDomain_singleFace_one_iff hnormal hZ).mp hx').1
  rw [← hnormal] at hx
  exact absurd h (not_lt.mpr (le_of_lt hx))

/-- Every endpoint is admitted by exactly one of the empty and one-crossing itineraries,
except those on a boundary event: the endpoints on the face and those whose crossing point
lies in the singular set. -/
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

section Codimension

variable [FiniteDimensional ℝ V]

/-- A closed singular set contained in an affine subspace of ambient codimension at least two
is nowhere dense in the face: every point of the face is a limit of points of the face
outside the singular set. -/
theorem face_subset_closure_diff_of_finrank (hν : ν ≠ 0) {E : AffineSubspace ℝ V}
    (hZE : Z ⊆ E) (hE : Module.finrank ℝ E.direction + 1 < Module.finrank ℝ V) :
    {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z) := by
  intro x hx
  have hx' : ν x = b := hx
  -- The face is the affine subspace through `x` with direction `ker ν`.
  let A : AffineSubspace ℝ V := .mk' x (LinearMap.ker ν.toLinearMap)
  have hA : ∀ y ∈ A, ν y = b := fun y hy => by
    have := AffineSubspace.mem_mk'.mp hy
    simpa [sub_eq_zero, hx'] using this
  have hdir : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V := by
    rw [AffineSubspace.direction_mk']
    exact Module.Dual.finrank_ker_add_one_of_ne_zero (f := ν.toLinearMap)
      (fun h => hν (ContinuousLinearMap.coe_injective h))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hzE⟩ := A.exists_mem_open_avoid_of_finrank_lt (fun _ : Unit => E)
    (fun _ => by omega) (U := Subtype.val ⁻¹' Metric.ball x ε)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
    ⟨⟨x, AffineSubspace.self_mem_mk' x _⟩, Metric.mem_ball_self hε⟩
  exact ⟨z, ⟨hA z z.2, fun hzZ => hzE () (hZE hzZ)⟩, by simpa [dist_comm] using hz⟩

end Codimension

end Mei.Convex
