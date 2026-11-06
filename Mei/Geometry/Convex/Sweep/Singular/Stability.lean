/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Singular
public import Mei.Geometry.Convex.Sweep.Degeneration
public import Mei.Geometry.Affine.Segment

/-!
# Stability of singular avoidance in backward families

If a weakly ordered backward path misses finitely many convex polyhedra, then
nearby endpoints satisfying the selected incidence and positive-time constraints
still satisfy singular avoidance. Thus a boundary of the singular-avoidance
domain is either a boundary of the selected itinerary domain or a path that
actually meets a singular cell. This includes contacts on the unbounded incoming
half-line: they cannot disappear to infinity while endpoints converge.

Finite segments use `IsClosed.isOpen_setOf_lineMap_notMem`. The incoming ray
uses the closed polyhedral negative-ray projection supplied by
`isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem`. No rationality,
transversality of the singular cells, or nonzero velocity is required.
The endpoint-chart interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V) (S : J → Set V)

local notation "u" => fun j : Fin n => v (Fin.castSucc j)
local notation "X" => backwardPoint f c u
local notation "T" => backwardTime f c u
local notation "τ" => backwardParameter f c u

/-- Singular avoidance persists near a weakly ordered path, relative to the
selected incidence and positive-time domain. Collapsed limiting segments and
zero incoming direction are allowed. -/
theorem eventually_mem_backwardSingularAvoidanceDomain
    (hS : ∀ a, TauCeti.IsConvexPolyhedron (S a)) {Q : V}
    (h0 : ∀ j, 0 ≤ T j Q)
    (havoid : ∀ a t, t ≤ 0 → backwardPath f c v Q t ∉ S a) :
    ∀ᶠ Q' in 𝓝 Q, Q' ∈ backwardDomain f c u P →
      Q' ∈ backwardSingularAvoidanceDomain f c v P S := by
  have hτ (j : Fin (n + 1)) : τ j Q ≤ 0 := by
    simpa only [backwardParameter_zero] using
      antitone_backwardParameter f c u Q h0 (Fin.zero_le j)
  -- Closed finite pieces are stable by compactness of their unit parameters.
  have hfinite : ∀ᶠ Q' in 𝓝 Q, ∀ (j : Fin n) a s, s ∈ Icc (0 : ℝ) 1 →
      AffineMap.lineMap (X j.castSucc Q') (X j.succ Q') s ∉ S a := by
    refine eventually_all.mpr fun j => eventually_all.mpr fun a => ?_
    apply ((X j.castSucc).continuous.prodMk (X j.succ).continuous).continuousAt
      |>.eventually ((hS a).isClosed.isOpen_setOf_lineMap_notMem.mem_nhds ?_)
    intro s hs
    rw [lineMap_backwardPoint]
    rw [← backwardPath_apply_segment f c v h0 j (mul_nonneg hs.1 (h0 j))
      (mul_le_of_le_one_left (h0 j) hs.2)]
    exact havoid a _ ((sub_le_self _ (mul_nonneg hs.1 (h0 j))).trans (hτ _))
  -- For the unbounded piece use closedness of the polyhedral ray projection.
  have hincoming : ∀ᶠ Q' in 𝓝 Q, ∀ a (s : ℝ), 0 ≤ s →
      X (Fin.last n) Q' + s • v (Fin.last n) ∉ S a := by
    refine eventually_all.mpr fun a => ?_
    have hc := (isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem
      (hS a) (v (Fin.last n))).isClosed
    have hnot : X (Fin.last n) Q ∉
        {x | ∃ s : ℝ, 0 ≤ s ∧ x + s • v (Fin.last n) ∈ S a} := by
      rintro ⟨s, hs, hmem⟩
      rw [← backwardPath_apply_incoming f c v h0 hs] at hmem
      exact havoid a _ ((sub_le_self _ hs).trans (hτ _)) hmem
    filter_upwards [(X (Fin.last n)).continuous.continuousAt.eventually
      (hc.isOpen_compl.mem_nhds hnot)] with Q' hQ' s hs
    exact fun hmem => hQ' ⟨s, hs, hmem⟩
  filter_upwards [hfinite, hincoming] with Q' hfinite hincoming hQ'
  have hpos (j) : 0 < T j Q' := ((mem_backwardDomain ..).mp hQ' j).1
  have hsegment (j : Fin n) (a : J) (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ T j Q') :
      X j.castSucc Q' + s • v j.castSucc ∉ S a := by
    have he := hfinite j a (s / T j Q')
      ⟨div_nonneg hs (hpos j).le, (div_le_one (hpos j)).mpr hs'⟩
    simpa only [lineMap_backwardPoint, div_mul_cancel₀ s (hpos j).ne'] using he
  apply (mem_backwardSingularAvoidanceDomain ..).mpr
  refine ⟨(mem_backwardAvoidanceDomain ..).mpr
    ⟨hQ', fun j a s hs hs' => hsegment j a s hs.le hs'.le⟩,
    (mem_backwardIncomingDomain ..).mpr
      ⟨hQ', fun a s hs => hincoming a s hs.le, by simp⟩, ?_⟩
  intro j a
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [zero_smul, add_zero] using hincoming a 0 le_rfl
  · simpa only [zero_smul, add_zero] using hsegment j a 0 le_rfl (hpos j).le

/-- A frontier point of singular avoidance either lies on the frontier of the
selected itinerary domain or has an actual singular contact at nonpositive time.
The contact may occur on the incoming half-line or at a recorded encounter. -/
theorem mem_frontier_backwardSingularAvoidanceDomain_imp
    (hS : ∀ a, TauCeti.IsConvexPolyhedron (S a)) {Q : V}
    (hQ : Q ∈ frontier (backwardSingularAvoidanceDomain f c v P S)) :
    Q ∈ frontier (backwardDomain f c u P) ∨
      ∃ a t, t ≤ 0 ∧ backwardPath f c v Q t ∈ S a := by
  by_cases hcontact : ∃ a t, t ≤ 0 ∧ backwardPath f c v Q t ∈ S a
  · exact Or.inr hcontact
  · left
    have hcl := closure_mono
      (backwardSingularAvoidanceDomain_subset_backwardDomain f c v P S)
      (frontier_subset_closure hQ)
    refine ⟨hcl, fun hint => ?_⟩
    have h0 (j) := ((mem_backwardDomain ..).mp (interior_subset hint) j).1.le
    have havoid : ∀ a t, t ≤ 0 → backwardPath f c v Q t ∉ S a := by
      simpa only [not_exists, not_and] using hcontact
    have hn := eventually_mem_backwardSingularAvoidanceDomain f c v P S hS h0 havoid
    have hi : Q ∈ interior (backwardSingularAvoidanceDomain f c v P S) := by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hn, mem_interior_iff_mem_nhds.mp hint] with Q' hnear hdom
      exact hnear hdom
    exact hQ.2 hi

end Mei.Convex
