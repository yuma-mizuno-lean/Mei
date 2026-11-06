/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Encounter.Bound
public import Mei.LinearAlgebra.ModuleFiltration.FiniteLength

/-!
# Geometric encounter bounds for component filtrations

A finite-length component filtration bounds the complete encounter count of
an actual decorated ray, provided an unmarked component preserves spatial
direction. The bound is `r * Nat.card J` for a filtration vanishing at order
`r` and a finite alphabet `J` of supporting hyperplanes. All encounters remain
recorded, including unchanged-degree encounters and changes of degree with
unchanged spatial direction. Coefficient degrees need not be ordered by a
positive monoid, and no bound on unmarked runs is assumed.

The last filtration membership order of each nonzero segment decoration gives
the rank of its straight piece. Component transfers make these ranks decrease
backwards; equal ranks force an unmarked component. We apply
`Convex.encounter_count_le_of_antitone_rank` to the original admissible ray.
This supplies the geometric part of the nilpotent-ideal finiteness argument in
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {n : ℕ} {T : J → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : O → Set V} {S : K → Set V} {C : Set V} {Q : V}
  {wall : Fin n → J}

/-- A nilpotent filtration and direction-preserving unmarked components bound
every recorded encounter. Marks may depend on the two component degrees and
may distinguish different components of the same wall operator. The coefficient
semiring and its modules need no cancellation or finiteness assumptions. -/
theorem encounter_count_le_of_filtration
    (β : DecoratedAdmissibleRay ℳ (fun j => T (wall j)) p₀ a v
      (fun j => f (wall j)) (fun j => c (wall j)) (fun j => ε (wall j))
      (fun j => P (wall j)) W S C Q)
    (F : ModuleFiltration R M) (w : J → Γ → Γ → ℕ)
    (hT : ∀ e i j k (x : M), x ∈ ℳ i → x ∈ F.submodule k →
      homogeneousComponent ℳ j (T e x) ∈ F.submodule (k + w e i j))
    (hstraight : ∀ e i j, w e i j = 0 → v i = v j)
    {r : ℕ} (hr : F.submodule r = ⊥) :
    n ≤ r * Nat.card J := by
  classical
  obtain ⟨rank, hrank⟩ := Classical.axiomOfChoice fun j : Fin (n + 1) =>
    F.exists_mem_notMem_succ hr (β.decoration_ne_zero j)
  let p := Fin.snoc (α := fun _ => Γ) β.1.val p₀
  have hstep (j : Fin n) :
      rank j.succ + w (wall j) (p j.succ) (p j.castSucc) ≤ rank j.castSucc := by
    have hmem : β.decoration j.succ ∈ ℳ (p j.succ) := by
      simpa only [decoration_def] using homogeneousHistoryStage_mem_snoc ℳ
        (fun j => T (wall j)) β.1.val p₀ a j.succ
    have hm := hT (wall j) (p j.succ) (p j.castSucc) (rank j.succ)
      (β.decoration j.succ) hmem (hrank j.succ).2.1
    have hout : β.decoration j.castSucc ∈
        F.submodule (rank j.succ + w (wall j) (p j.succ) (p j.castSucc)) := by
      rw [β.decoration_castSucc]
      simpa only [p, Fin.snoc_castSucc, homogeneousComponent_apply] using hm
    by_contra h
    exact (hrank j.castSucc).2.2
      (F.antitone (by omega) hout)
  have hanti : Antitone rank := Fin.antitone_iff_succ_le.mpr fun j =>
    (Nat.le_add_right _ _).trans (hstep j)
  obtain ⟨hpos, _, _⟩ := β.2.eq_backwardRay
  apply Convex.encounter_count_le_of_antitone_rank f c wall (fun j => v (p j)) Q
    hpos β.2.transverse rank hanti (hrank 0).1
  intro j hj
  have hz : w (wall j) (p j.succ) (p j.castSucc) = 0 := by
    have := hstep j
    omega
  exact (hstraight _ _ _ hz).symm

end Mei.DecoratedAdmissibleRay
