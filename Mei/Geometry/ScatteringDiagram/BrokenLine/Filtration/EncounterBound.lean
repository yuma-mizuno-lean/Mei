/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.Geometry

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
  let p := Fin.snoc (α := fun _ => Γ) β.1.val p₀
  apply β.2.encounter_count_le_of_filtration (fun _ => F) β.decoration
    β.decoration_ne_zero (fun j => w (wall j) (p j.succ) (p j.castSucc))
    (fun j k hk => ?_) (fun j hj => (hstraight _ _ _ hj).symm) (fun _ => hr)
  · rename_i j k hk
    have hmem : β.decoration j.succ ∈ ℳ (p j.succ) := by
      simpa only [decoration_def] using homogeneousHistoryStage_mem_snoc ℳ
        (fun j => T (wall j)) β.1.val p₀ a j.succ
    have hm := hT (wall j) (p j.succ) (p j.castSucc) k
      (β.decoration j.succ) hmem hk
    rw [β.decoration_castSucc]
    simpa only [p, Fin.snoc_castSucc, homogeneousComponent_apply] using hm

end Mei.DecoratedAdmissibleRay
