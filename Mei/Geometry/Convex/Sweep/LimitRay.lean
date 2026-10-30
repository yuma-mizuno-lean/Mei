/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Degeneration
public import Mei.Geometry.Affine.FiniteRay.Nonpos

/-!
# Finite affine rays at collapsed encounters

With nonnegative elapsed times, the continuous hinge extension of a backward
itinerary is still a finite affine ray on the negative half-line. Coincident
encounter times add their direction increments; zero-time increments become part
of the final direction. The recorded encounters retain their affine positions,
even when several coincide. No admissibility or coefficient propagation at these
limiting encounters is asserted.

This identifies the geometric limit of strict realizations with an actual finite
ray, including terminal and multiple-encounter collapses. It combines
`backwardPath`, `backwardRay`, and `FiniteAffineRay.ofNonposBends`. The backward
parameterization follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg
models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin (n + 1) → V)

local notation "τ" => backwardParameter f c (fun j : Fin n => v (Fin.castSucc j))
local notation "Δ" j => v (Fin.succ j) - v (Fin.castSucc j)

/-- The finite ray associated to a weakly ordered itinerary. The bends at equal
negative times are combined and time-zero increments are absorbed into its final
direction. Its continuation at positive times need not equal `backwardPath`. -/
def backwardLimitRay (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    FiniteAffineRay V V := by
  classical
  refine FiniteAffineRay.ofNonposBends Q (v 0)
    (∑ j : Fin n, Finsupp.single (τ j.succ Q) (Δ j)) ?_
  intro t ht
  obtain ⟨j, _, ht⟩ := Finsupp.mem_support_finsetSum t ht
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  rw [he]
  simpa using antitone_backwardParameter f c (fun j => v j.castSucc) Q hQ (Fin.zero_le j.succ)

/-- The limiting finite ray has the limiting endpoint. -/
@[simp]
theorem endpoint_backwardLimitRay (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    (backwardLimitRay f c v Q hQ).endpoint = Q := by
  rw [backwardLimitRay, FiniteAffineRay.endpoint_ofNonposBends]

/-- The bend data sum all increments at each encounter parameter, then remove
time zero. Cancellation may remove a geometric bend without removing an encounter. -/
@[simp]
theorem bends_backwardLimitRay (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    (backwardLimitRay f c v Q hQ).bends =
      (∑ j : Fin n, Finsupp.single (τ j.succ Q) (Δ j)).erase 0 := by
  rw [backwardLimitRay, FiniteAffineRay.bends_ofNonposBends]

/-- The limiting ray agrees with the continuous hinge extension on its entire
negative half-line, including the endpoint and collapsed encounters. -/
theorem backwardLimitRay_apply (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q)
    {t : ℝ} (ht : t ≤ 0) :
    backwardLimitRay f c v Q hQ t = backwardPath f c v Q t := by
  classical
  rw [backwardLimitRay, FiniteAffineRay.ofNonposBends_apply _ _ _ _ ht,
    ← Finsupp.sum_finsetSum_index (fun b => smul_zero (max (b - t) 0))
      (fun b x y => smul_add (max (b - t) 0) x y)]
  simp only [Finsupp.sum_single_index (h := fun b (x : V) => max (b - t) 0 • x)
    (smul_zero _), vadd_eq_add, backwardPath_apply]

/-- The final direction incorporates exactly the increments whose encounters
have collapsed onto the endpoint. -/
theorem direction_backwardLimitRay (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    (backwardLimitRay f c v Q hQ).direction =
      v 0 + ∑ j : Fin n, if τ j.succ Q = 0 then Δ j else 0 := by
  classical
  simp only [backwardLimitRay, FiniteAffineRay.direction_ofNonposBends,
    Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The incoming direction is unchanged even if any number of encounters collapse. -/
@[simp]
theorem incomingDirection_backwardLimitRay (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    (backwardLimitRay f c v Q hQ).incomingDirection = v (Fin.last n) := by
  classical
  rw [backwardLimitRay, FiniteAffineRay.incomingDirection_ofNonposBends,
    ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index (h := fun _ (x : V) => x) rfl]
  cases n with
  | zero => simp
  | succ m =>
    have he := Fin.sum_Iic_sub (Fin.last m) v
    have hall : Finset.Iic (Fin.last m) = Finset.univ := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last _
    rw [hall] at he
    rw [he]
    abel

/-- At negative time the geometric bend is exactly the sum of all direction
increments in that collision block, provided that sum does not cancel. -/
theorem mem_bends_support_backwardLimitRay_iff (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) (t : ℝ) :
    t ∈ (backwardLimitRay f c v Q hQ).bends.support ↔
      t < 0 ∧ (∑ j : Fin n, if τ j.succ Q = t then Δ j else 0) ≠ 0 := by
  classical
  have he (ht : t ≠ 0) : (backwardLimitRay f c v Q hQ).bends t =
      ∑ j : Fin n, if τ j.succ Q = t then Δ j else 0 := by
    simp only [bends_backwardLimitRay, Finsupp.erase_ne ht,
      Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro ht
    have hneg := (backwardLimitRay f c v Q hQ).bend_neg t ht
    exact ⟨hneg, he hneg.ne ▸ Finsupp.mem_support_iff.mp ht⟩
  · rintro ⟨ht, hn⟩
    rw [Finsupp.mem_support_iff, he ht.ne]
    exact hn

/-- Every recorded encounter retains its affine position, including encounters
at the endpoint and several encounters at the same parameter. -/
@[simp]
theorem backwardLimitRay_apply_parameter (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q)
    (j : Fin (n + 1)) :
    backwardLimitRay f c v Q hQ (τ j Q) =
      backwardPoint f c (fun j => v j.castSucc) j Q := by
  have ht : τ j Q ≤ 0 := by
    simpa using antitone_backwardParameter f c (fun j => v j.castSucc) Q hQ (Fin.zero_le j)
  rw [backwardLimitRay_apply f c v Q hQ ht, backwardPath_apply_parameter f c v hQ]

/-- On strict itineraries, normalization recovers the existing realization as a
finite ray, including its continuation past time zero. -/
theorem backwardLimitRay_eq_backwardRay (Q : V)
    (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q) :
    backwardLimitRay f c v Q (fun j => (hpos j).le) = backwardRay f c v Q hpos := by
  rw [backwardLimitRay]
  simpa only [endpoint_backwardRay, direction_backwardRay, bends_backwardRay] using
    FiniteAffineRay.ofNonposBends_eq (backwardRay f c v Q hpos)

/-- Converging strict realizations converge to the normalized limiting finite ray
in the compact-open topology on the closed negative half-line. No convergence of
their affine continuations past the endpoint is asserted. -/
theorem tendsto_backwardRay_restrict {A : Type*} {l : Filter A} {Q : A → V} {Q₀ : V}
    (hQ : Tendsto Q l (𝓝 Q₀))
    (hpos : ∀ a j, 0 < backwardTime f c (fun j => v j.castSucc) j (Q a))
    (hQ₀ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q₀) :
    Tendsto (fun a => (backwardRay f c v (Q a) (hpos a)).toContinuousMap.restrict (Iic 0)) l
      (𝓝 ((backwardLimitRay f c v Q₀ hQ₀).toContinuousMap.restrict (Iic 0))) := by
  have he : (backwardPath f c v Q₀).restrict (Iic 0) =
      (backwardLimitRay f c v Q₀ hQ₀).toContinuousMap.restrict (Iic 0) := by
    ext t
    simpa only [ContinuousMap.restrict_apply, FiniteAffineRay.toContinuousMap_apply] using
      (backwardLimitRay_apply f c v Q₀ hQ₀ t.property).symm
  rw [← he]
  exact ContinuousMap.tendsto_compactOpen_restrict
    (tendsto_backwardRay f c v hQ hpos) (Iic 0)

end Mei.Convex
