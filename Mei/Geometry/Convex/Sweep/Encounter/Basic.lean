/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization
public import Mei.Geometry.Convex.Sweep.Avoidance
public import Mei.Geometry.Convex.Sweep.Incoming

/-!
# Wall encounters of realized backward itineraries

The finite-segment and incoming-ray avoidance constraints on an endpoint are
equivalent to the absence of wall encounters at every negative path parameter
other than the recorded encounter times. If each selected support is a wall
support, these are exactly all the wall encounters, including encounters with
unchanged direction. The endpoint is tested separately.

Eventual admission of the incoming ray to a source is also equivalent to eventual
admission of the continuous realization at negative infinity. Thus the existing
semilinear endpoint domains characterize these conditions on the full continuous
path. Endpoint restrictions, singular-set avoidance at recorded encounters,
coefficient propagation and finiteness of decorated itineraries are separate questions.

We use `backwardRay_apply_segment` and `backwardRay_apply_incoming` to identify
the realization with the affine charts. The backward parameterization follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (Q : V)
  (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q)

local notation "τ" => fun j : Fin (n + 1) =>
  backwardParameter f c (fun l : Fin n => v (Fin.castSucc l)) j Q
local notation "X" => fun j : Fin (n + 1) =>
  backwardPoint f c (fun l : Fin n => v (Fin.castSucc l)) j Q
local notation "β" => backwardRay f c v Q hpos

/-- Every negative parameter away from recorded encounters belongs either to the
open incoming half-line or to one of the open finite segments. -/
private theorem backwardParameter_cases {t : ℝ} (ht : t < 0)
    (hne : ∀ j : Fin n, t ≠ τ j.succ) :
    t < τ (Fin.last n) ∨ ∃ j : Fin n, τ j.succ < t ∧ t < τ j.castSucc := by
  have hcover (j : Fin (n + 1)) (hj : t < τ j) :
      t < τ (Fin.last n) ∨ ∃ j : Fin n, τ j.succ < t ∧ t < τ j.castSucc := by
    induction j using Fin.reverseInduction with
    | last => exact Or.inl hj
    | cast j ih =>
      by_cases hs : t < τ j.succ
      · exact ih hs
      · exact Or.inr ⟨j, lt_of_le_of_ne (le_of_not_gt hs) (hne j).symm, hj⟩
  exact hcover 0 (by simpa using ht)

/-- Global wall avoidance away from the recorded encounters is exactly the
finite open-segment constraints together with the open incoming-ray constraints.
No convexity or transversality hypothesis on the avoided sets is needed. -/
theorem backwardRay_avoids_iff (W : J → Set V) :
    (∀ a t, t < 0 → (∀ j : Fin n, t ≠ τ j.succ) → β t ∉ W a) ↔
      (∀ j a s, 0 < s → s < backwardTime f c (fun j => v j.castSucc) j Q →
        X j.castSucc + s • v j.castSucc ∉ W a) ∧
      (∀ a (s : ℝ), 0 < s → X (Fin.last n) + s • v (Fin.last n) ∉ W a) := by
  have hanti := strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos
  have hnonpos (j : Fin (n + 1)) : τ j ≤ 0 := by
    simpa using hanti.antitone (Fin.zero_le j)
  constructor
  · intro h
    constructor
    · intro j a s hs hs'
      let t := τ j.castSucc - s
      have hlo : τ j.succ < t := by
        dsimp [t]
        rw [backwardParameter_succ]
        linarith
      have hhi : t < τ j.castSucc := sub_lt_self _ hs
      have hne (l : Fin n) : t ≠ τ l.succ := by
        by_cases hlj : l < j
        · have hlj' : l.succ ≤ j.castSucc := by
            simpa only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] using
              Nat.succ_le_iff.mpr hlj
          have hl := hanti.antitone hlj'
          linarith
        · have hjl : j.succ ≤ l.succ := by simpa using le_of_not_gt hlj
          have hl := hanti.antitone hjl
          linarith
      have he := backwardRay_apply_segment f c v Q hpos j t hlo.le hhi.le
      have ht : t < 0 := hhi.trans_le (hnonpos j.castSucc)
      have := h a t ht hne
      rw [he] at this
      simpa only [t, sub_sub_cancel] using this
    · intro a s hs
      let t := τ (Fin.last n) - s
      have ht : t < τ (Fin.last n) := sub_lt_self _ hs
      have hne (j : Fin n) : t ≠ τ j.succ := by
        have hj := hanti.antitone (Fin.le_last j.succ)
        linarith
      have := h a t (ht.trans_le (hnonpos _)) hne
      rw [backwardRay_apply_incoming f c v Q hpos t ht.le] at this
      simpa only [t, sub_sub_cancel] using this
  · rintro ⟨hfinite, hincoming⟩ a t ht hne
    rcases backwardParameter_cases f c v Q ht hne with hi | ⟨j, hlo, hhi⟩
    · rw [backwardRay_apply_incoming f c v Q hpos t hi.le]
      exact hincoming a _ (sub_pos.mpr hi)
    · rw [backwardRay_apply_segment f c v Q hpos j t hlo.le hhi.le]
      apply hfinite j a _ (sub_pos.mpr hhi)
      simp only [backwardParameter_succ] at hlo
      linarith

/-- The intersection of the finite and incoming endpoint domains characterizes
selected incidences, absence of every unrecorded wall encounter, and eventual
source admission on the actual continuous path. The endpoint itself is excluded
from the encounter test. -/
theorem mem_backwardAvoidanceDomain_inter_incoming_iff
    (P : Fin n → Set V) (W : J → Set V) (C : Set V) :
    Q ∈ backwardAvoidanceDomain f c (fun j => v j.castSucc) P W ∩
      backwardIncomingDomain f c (fun j => v j.castSucc) P (v (Fin.last n)) C W ↔
      (∀ j : Fin n, β (τ j.succ) ∈ P j) ∧
      (∀ a t, t < 0 → (∀ j : Fin n, t ≠ τ j.succ) → β t ∉ W a) ∧
      ∀ᶠ t : ℝ in atBot, β t ∈ C := by
  rw [backwardRay_avoids_iff, backwardRay_eventually_mem_iff]
  simp only [Set.mem_inter_iff, mem_backwardAvoidanceDomain, mem_backwardIncomingDomain,
    mem_backwardDomain, backwardRay_apply_parameter]
  constructor
  · rintro ⟨⟨hP, hfinite⟩, _, hincoming, hsource⟩
    exact ⟨fun j => (hP j).2, ⟨hfinite, hincoming⟩, hsource⟩
  · rintro ⟨hP, ⟨hfinite, hincoming⟩, hsource⟩
    exact ⟨⟨fun j => ⟨hpos j, hP j⟩, hfinite⟩,
      ⟨fun j => ⟨hpos j, hP j⟩, hincoming, hsource⟩⟩

/-- If all selected supports belong to the wall family, the negative parameters
at which the realized path meets any wall are exactly the recorded times.
Simultaneous walls and encounters with unchanged velocity are retained. -/
theorem backwardRay_mem_wall_iff (P : Fin n → Set V) (W : J → Set V)
    (hQ : Q ∈ backwardAvoidanceDomain f c (fun j => v j.castSucc) P W)
    (hincoming : ∀ a (s : ℝ), 0 < s → X (Fin.last n) + s • v (Fin.last n) ∉ W a)
    (hP : ∀ j, P j ⊆ ⋃ a, W a) {t : ℝ} (ht : t < 0) :
    (∃ a, β t ∈ W a) ↔ ∃ j : Fin n, t = τ j.succ := by
  obtain ⟨hselected, hfinite⟩ := (mem_backwardAvoidanceDomain _ _ _ _ _ _).mp hQ
  have havoid := (backwardRay_avoids_iff f c v Q hpos W).mpr ⟨hfinite, hincoming⟩
  constructor
  · intro hwall
    by_contra h
    obtain ⟨a, ha⟩ := hwall
    exact havoid a t ht (by simpa only [not_exists] using h) ha
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mp (hP j (by
      rw [backwardRay_apply_parameter]
      exact ((mem_backwardDomain _ _ _ _ _).mp hselected j).2))

end Mei.Convex
