/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Encounter bounds from a finite order of straight pieces

A transverse backward itinerary with a nonincreasing natural rank has at most
`r * Nat.card J` encounters if its ranks are below `r`. Equal adjacent ranks must
preserve direction. Each wall then occurs at most once at any rank, even when
degrees or directions recur at different ranks. No positive monoid or
monotonicity of coefficient degrees is required.

This generalizes the no-repetition argument of
`nodup_of_mem_realizedDegreeItineraries`, replacing positive degree by an
independent finite rank. We reuse `backwardPoint_eq_add_of_constant`: encounters at a common
rank lie on one straight piece, on which a transverse supporting hyperplane has
only one intersection. This is the straight-piece bound in the finiteness
argument of Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4).
-/

public section

namespace Mei.Convex

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A rank that changes whenever direction changes bounds all transverse
encounters with a finite wall alphabet. Repeated wall labels and
unchanged-direction encounters are retained. -/
theorem encounter_count_le_of_antitone_rank [Finite J] {n r : ℕ}
    (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (wall : Fin n → J)
    (v : Fin (n + 1) → V) (Q : V)
    (hpos : ∀ j, 0 < backwardTime (fun j => f (wall j)) (fun j => c (wall j))
      (fun j => v j.castSucc) j Q)
    (htrans : ∀ j, f (wall j) (v j.castSucc) ≠ 0)
    (rank : Fin (n + 1) → ℕ) (hanti : Antitone rank) (hr : rank 0 < r)
    (hstraight : ∀ j : Fin n, rank j.castSucc = rank j.succ → v j.castSucc = v j.succ) :
    n ≤ r * Nat.card J := by
  let F := fun j => f (wall j)
  let offset := fun j => c (wall j)
  let u := fun j : Fin n => v j.castSucc
  let encode (j : Fin n) : Fin r × J :=
    (⟨rank j.succ, lt_of_le_of_lt (hanti (Fin.zero_le _)) hr⟩, wall j)
  -- Encode an encounter by its incoming straight-piece rank and wall label.
  have hinj : Function.Injective encode := by
    intro a b hab
    have hrank : rank a.succ = rank b.succ := congrArg (fun z : Fin r × J => z.1.val) hab
    have hwall : wall a = wall b := congrArg Prod.snd hab
    have hne {a b : Fin n} (hab : a < b)
        (hrank : rank a.succ = rank b.succ) (hwall : wall a = wall b) : False := by
      -- A fiber of an antitone rank is an interval of constant direction.
      have heq (j : Fin (n + 1)) (haj : a.succ ≤ j) (hjb : j ≤ b.succ) :
          rank j = rank a.succ :=
        le_antisymm (hanti haj) (hrank ▸ hanti hjb)
      have hconstant (j : Fin (n + 1)) (haj : a.succ ≤ j) (hjb : j ≤ b.succ) :
          v j = v a.succ := by
        induction j using Fin.induction with
        | zero => exact (not_le_of_gt (Fin.succ_pos a) haj).elim
        | succ j ih =>
          by_cases he : a.succ = j.succ
          · exact congrArg v he.symm
          have hle : a.succ ≤ j.castSucc := by
            simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc,
              Fin.ext_iff] at haj he ⊢
            omega
          exact (hstraight j ((heq _ hle ((Fin.castSucc_le_succ j).trans hjb)).trans
            (heq _ haj hjb).symm)).symm.trans
              (ih hle ((Fin.castSucc_le_succ j).trans hjb))
      -- Two visits to the same supporting hyperplane on this piece would
      -- contradict transversality and strict ordering of the parameters.
      have hb := backwardPoint_height F offset u b (htrans b) Q
      have hheight : F a (backwardPoint F offset u b.succ Q) = offset a := by
        simpa only [F, offset, hwall] using hb
      have hv : F a (v a.succ) ≠ 0 := by
        have hdir := hconstant b.castSucc (by simpa using hab)
          (Fin.castSucc_le_succ b)
        simpa only [F, ← hwall, hdir] using htrans b
      exact backwardPoint_height_ne_of_constant F offset u Q hpos a b hab (htrans a)
        (v a.succ) (fun j haj hjb =>
          hconstant j.castSucc haj ((Fin.castSucc_le_succ j).trans hjb)) hv hheight
    rcases lt_trichotomy a b with h | h | h
    · exact (hne h hrank hwall).elim
    · exact h
    · exact (hne h hrank.symm hwall.symm).elim
  simpa only [Nat.card_fin, Nat.card_prod] using Nat.card_le_card_of_injective encode hinj

end Mei.Convex
