/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Limit
public import Mei.Geometry.Convex.Sweep.Contact

/-!
# New wall contacts in limiting admissible rays

In the interior of a finite segment or of the incoming half-line, a transverse
wall contact of a limiting admissible ray lies on the wall's relative boundary,
hence in singular support. This rules out new transverse regular encounters
away from the recorded encounter parameters. Recorded encounters and collapsed
segments are separate boundary events.

The statements use the original full admissible endpoint domain, so they retain
its incoming source and all wall and singular avoidance conditions. No finite
wall inventory, rationality, convexity or closedness of the walls is needed.
Each wall's affine span is its prescribed supporting hyperplane.

We apply `ContinuousLinearMap.notMem_intrinsicInterior_of_mem_closure_of_avoids`
to the affine segment formulas of `backwardPath`. This is part of the closed
endpoint-chart interpretation of Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Mei.Convex

namespace Mei.Convex

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "D" => admissibleBackwardDomain f c v P W S C
local notation "τ" => backwardParameter f c (fun j : Fin n => v (Fin.castSucc j))
local notation "X" => backwardPoint f c (fun j : Fin n => v (Fin.castSucc j))

/-- A new transverse wall contact strictly inside a limiting finite segment
belongs to the relative boundary of that wall. The segment length remains
strictly greater than the contact parameter. -/
theorem backwardPath_mem_intrinsicFrontier_of_segment_contact
    {Q : V} (hQ : Q ∈ closure D) (j : Fin n) {s : ℝ} (hs : 0 < s)
    (hs' : s < backwardTime f c (fun j => v j.castSucc) j Q)
    (a : J) (ν : V →L[ℝ] ℝ) (b : ℝ)
    (hspan : (affineSpan ℝ (W a) : Set V) = {x | ν x = b})
    (hv : ν (v j.castSucc) ≠ 0)
    (hhit : backwardPath f c v Q (τ j.castSucc Q - s) ∈ W a) :
    backwardPath f c v Q (τ j.castSucc Q - s) ∈ intrinsicFrontier ℝ (W a) := by
  have he := backwardPath_apply_segment f c v
    (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ)
    j hs.le hs'.le
  rw [he] at hhit ⊢
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  refine ⟨subset_intrinsicClosure hhit, ?_⟩
  exact ν.notMem_intrinsicInterior_of_mem_closure_of_avoids hspan hv
    (X j.castSucc).continuous.continuousAt continuousAt_const
    (backwardTime f c (fun j => v j.castSucc) j).continuous.continuousAt
    (fun Q' hQ' t ht ht' =>
      ((mem_backwardAvoidanceDomain ..).mp
        ((mem_admissibleBackwardDomain ..).mp hQ').1).2 j a t ht ht') hQ hs hs'

/-- A new transverse contact on the open incoming half-line of a limiting ray
lies on the relative boundary of the wall. The full incoming tail is retained. -/
theorem backwardPath_mem_intrinsicFrontier_of_incoming_contact
    {Q : V} (hQ : Q ∈ closure D) {s : ℝ} (hs : 0 < s)
    (a : J) (ν : V →L[ℝ] ℝ) (b : ℝ)
    (hspan : (affineSpan ℝ (W a) : Set V) = {x | ν x = b})
    (hv : ν (v (Fin.last n)) ≠ 0)
    (hhit : backwardPath f c v Q (τ (Fin.last n) Q - s) ∈ W a) :
    backwardPath f c v Q (τ (Fin.last n) Q - s) ∈ intrinsicFrontier ℝ (W a) := by
  have he := backwardPath_apply_incoming f c v
    (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ) hs.le
  rw [he] at hhit ⊢
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  refine ⟨subset_intrinsicClosure hhit, ?_⟩
  exact ν.notMem_intrinsicInterior_of_mem_closure_of_avoids hspan hv
    (X (Fin.last n)).continuous.continuousAt continuousAt_const
    (b := fun _ => s + 1) continuousAt_const
    (fun Q' hQ' t ht _ =>
      ((mem_backwardIncomingDomain ..).mp
        ((mem_admissibleBackwardDomain ..).mp hQ').2.1).2.1 a t ht)
    hQ hs (lt_add_one s)

end Mei.Convex
