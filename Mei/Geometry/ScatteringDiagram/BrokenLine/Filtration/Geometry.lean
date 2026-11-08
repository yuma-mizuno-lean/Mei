/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Sweep.Encounter.Bound
public import Mei.LinearAlgebra.ModuleFiltration.FiniteLength

/-!
# Encounter bounds with different coefficient modules on successive segments

A developed admissible ray can carry decorations in different chamber modules.
Filtration orders can still be compared across encounters: each selected transfer
preserves order and marked transfers increase it. If unmarked encounters preserve
the developed direction, a filtration of length `r` bounds the full encounter word
by `r * Nat.card J`. No identification of the chamber modules is needed.

The argument ranks straight pieces by the last filtration order of their nonzero
decorations and uses `Convex.encounter_count_le_of_antitone_rank`. All encounters
are counted, including those preserving decorations or spatial direction. This
is the straight-piece argument of Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

variable {R V J K O : Type*} [Semiring R]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {n : ℕ} {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {wall : Fin n → J}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : O → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- A finite-length filtration on each segment's coefficient module bounds the
complete encounter word. The transfer estimate is required only for the actual
decoration, at every possible input order. Marks may depend on the selected
component, and unmarked steps must preserve the developed spatial direction. -/
theorem encounter_count_le_of_filtration
    (β : AdmissibleRayRealization (fun j => f (wall j)) (fun j => c (wall j))
      v P W S C Q)
    {M : Fin (n + 1) → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (F : ∀ j, ModuleFiltration R (M j)) (a : ∀ j, M j)
    (ha : ∀ j, a j ≠ 0) (w : Fin n → ℕ)
    (hstep : ∀ j k, a j.succ ∈ (F j.succ).submodule k →
      a j.castSucc ∈ (F j.castSucc).submodule (k + w j))
    (hstraight : ∀ j, w j = 0 → v j.castSucc = v j.succ)
    {r : ℕ} (hr : ∀ j, (F j).submodule r = ⊥) :
    n ≤ r * Nat.card J := by
  obtain ⟨rank, hrank⟩ := Classical.axiomOfChoice fun j : Fin (n + 1) =>
    (F j).exists_mem_notMem_succ (hr j) (ha j)
  have horder (j : Fin n) : rank j.succ + w j ≤ rank j.castSucc := by
    have hm := hstep j (rank j.succ) (hrank j.succ).2.1
    by_contra h
    exact (hrank j.castSucc).2.2 ((F j.castSucc).antitone (by omega) hm)
  have hanti : Antitone rank := Fin.antitone_iff_succ_le.mpr fun j =>
    (Nat.le_add_right _ _).trans (horder j)
  obtain ⟨hpos, _, _⟩ := β.eq_backwardRay
  apply Convex.encounter_count_le_of_antitone_rank f c wall v Q hpos β.transverse
    rank hanti (hrank 0).1
  intro j hj
  exact hstraight j (by have := horder j; omega)

end Mei.Convex.AdmissibleRayRealization
