/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Contact
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Wall avoidance in regular limits of backward rays

A limit of admissible backward rays has no additional wall encounters if its
endpoint misses the walls and its negative half-line misses singular support.
Transverse contacts are excluded by persistence of relative-interior crossings.
For a tangential contact, the straight segment to its recorded base point lies
in the wall's affine span. Regularity propagates wall membership to that base
point. At the endpoint this contradicts allowedness; at a recorded encounter
it contradicts preservation of a nonzero normal velocity.

The incoming half-line is included. Selected supports may be nonclosed subsets
of closed ambient walls, so simultaneous encounters retain their full supports.
No convexity, rationality or finite wall inventory is required. This extends
the closed-path boundary analysis of Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2), using
`Convex.inter_affineSpan_subset_of_disjoint_singularSupport`.
-/

public section

open Set Mei.Convex

namespace Mei.Convex

variable {V K O : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : O → Set V) (S : K → Set V) (C : Set V)

local notation "D" => admissibleBackwardDomain f c v P W S C
local notation "τ" => backwardParameter f c (fun j : Fin n => v (Fin.castSucc j))
local notation "X" => backwardPoint f c (fun j : Fin n => v (Fin.castSucc j))

/-- Every open segment of a regular limiting ray, including its incoming tail,
misses all unrecorded walls. Preserving normal velocity prevents a segment from
departing tangentially along a different wall at a regular recorded encounter. -/
theorem backwardPath_notMem_wall_of_regular_limit
    (wall : Fin n → O) (hclosed : ∀ a, IsClosed (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (htrans : ∀ j, f j (v j.succ) ≠ 0)
    (ν : O → V →L[ℝ] ℝ) (b : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = b a})
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ t ≤ 0, backwardPath f c v Q t ∉ singularSupport W)
    (j : Fin (n + 1)) {s : ℝ} (hs : 0 < s)
    (hs' : ∀ e : Fin n, j = e.castSucc →
      s < backwardTime f c (fun l => v l.castSucc) e Q) (a : O) :
    backwardPath f c v Q (τ j Q - s) ∉ W a := by
  have h0 := backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain
    f c v P W S C hQ
  have hτ (l : Fin (n + 1)) : τ l Q ≤ 0 := by
    simpa using antitone_backwardParameter f c (fun l => v l.castSucc) Q h0 (Fin.zero_le l)
  have hline (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ s) :
      backwardPath f c v Q (τ j Q - r) = X j Q + r • v j := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨e, rfl⟩ | rfl
    · exact backwardPath_apply_segment f c v h0 e hr (hr'.trans (hs' e rfl).le)
    · exact backwardPath_apply_incoming f c v h0 hr
  intro hhit
  by_cases hv : ν a (v j) ≠ 0
  · -- A transverse open-segment contact is a relative-boundary point.
    apply hregular (τ j Q - s) ((sub_le_self _ hs.le).trans (hτ j))
    apply mem_singularSupport.mpr
    left
    refine ⟨a, ?_⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨e, rfl⟩ | rfl
    · exact backwardPath_mem_intrinsicFrontier_of_segment_contact f c v P W S C
        hQ e hs (hs' e rfl) a (ν a) (b a) (hspan a) hv hhit
    · exact backwardPath_mem_intrinsicFrontier_of_incoming_contact f c v P W S C
        hQ hs a (ν a) (b a) (hspan a) hv hhit
  · -- Along a tangent line, regularity propagates membership back to the base.
    have hv : ν a (v j) = 0 := not_ne_iff.mp hv
    let g : ℝ →ᵃ[ℝ] V := AffineMap.lineMap (X j Q) (X j Q + v j)
    have hg (r : ℝ) : g r = X j Q + r • v j := by
      simp [g, AffineMap.lineMap_apply_module', add_comm]
    have hK : Convex ℝ (g '' Icc 0 s) := (convex_Icc (0 : ℝ) s).affine_image g
    have hdisj : Disjoint (g '' Icc 0 s) (singularSupport W) := by
      apply disjoint_left.mpr
      rintro _ ⟨r, hr, rfl⟩ hsing
      apply hregular (τ j Q - r) ((sub_le_self _ hr.1).trans (hτ j))
      rwa [hline r hr.1 hr.2, ← hg]
    have hhit' : g s ∈ W a := by rwa [hline s hs.le le_rfl, ← hg] at hhit
    have hxspan : X j Q ∈ affineSpan ℝ (W a) := by
      have hh := (hspan a).subset (subset_affineSpan ℝ _ hhit')
      rw [hg] at hh
      apply (hspan a).symm.subset
      simpa only [mem_ofPred_eq, map_add, map_smul, hv, smul_zero, add_zero] using hh
    have hx : X j Q ∈ W a := hK.inter_affineSpan_subset_of_disjoint_singularSupport
      hdisj ⟨g s, ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩, hhit'⟩
      ⟨⟨0, ⟨le_rfl, hs.le⟩, by simp [hg]⟩, hxspan⟩
    -- A regular recorded base lies on the selected wall with nonzero incoming normal.
    induction j using Fin.cases with
    | zero => exact hoff a (by simpa using hx)
    | succ e =>
      have hinc : X e.succ Q ∈ W (wall e) := by
        exact closure_minimal (s := D) (t := (X e.succ) ⁻¹' W (wall e)) (fun Y hY =>
          hP e (((mem_backwardDomain ..).mp
            (admissibleBackwardDomain_subset_backwardDomain f c v P W S C hY) e).2))
          ((hclosed _).preimage (X e.succ).continuous) hQ
      have hreg : X e.succ Q ∉ singularSupport W := by
        simpa only [backwardPath_apply_parameter f c v h0] using hregular (τ e.succ Q) (hτ _)
      have heq := affineSpan_eq_of_notMem_singularSupport hreg hx hinc
      have hxv : X e.succ Q + v e.succ ∈ affineSpan ℝ (W (wall e)) := by
        rw [← heq]
        apply (hspan a).symm.subset
        have hhx : ν a (X e.succ Q) = b a := (hspan a).subset hxspan
        simpa only [mem_ofPred_eq, map_add, hv, add_zero] using hhx
      have hh := AffineMap.eqOn_affineSpan
        (f := (f e).toLinearMap.toAffineMap) (g := AffineMap.const ℝ V (c e)) (hheight e) hxv
      have hz : f e (v e.succ) = 0 := by
        simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
          AffineMap.const_apply, map_add, hheight e _ hinc, add_eq_left] using hh
      exact htrans e hz

end Mei.Convex
