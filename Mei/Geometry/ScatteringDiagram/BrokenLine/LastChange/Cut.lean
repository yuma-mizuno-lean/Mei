/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cut
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization

/-!
# Incoming cuts at the canonical last degree change

Combine `CutoffDecoratedRay.lastChangeIndex_spec` with the generic incoming-cut
construction to obtain the smaller-cutoff incoming piece of the last-change
recursion in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex Set

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

namespace CutoffDecoratedRay

/-- Every ray with nonzero final relative degree has an actual incoming cut
before its canonical last degree change, belonging to a strictly smaller cutoff.
The whole incoming decoration and every older encounter are retained, even when
the selected degree change does not change spatial velocity. The selected
encounter and all later unchanged-degree encounters are discarded. -/
theorem exists_lastChange_cutoff_truncate
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hq : r.finalDegree ≠ 0) :
    let j := r.lastChangeIndex hq
    ∃ t < r.realization.2.parameter j.succ,
      ∃ l < (d.degree r.finalDegree).toNat,
        ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (r.realization.2.ray t),
          b.itinerary = r.itinerary.drop (j.val + 1) ∧
          b.realization.2.ray = r.realization.2.ray.truncate t ∧
          b.decoration = r.realization.decoration j.succ ∧
          b.finalDegree = Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ := by
  dsimp only
  let j := r.lastChangeIndex hq
  have cut : ∃ t < r.realization.2.parameter j.succ,
      ∀ i : Fin r.itinerary.length, j < i → r.realization.2.parameter i.succ < t := by
    by_cases hj : j.succ = Fin.last r.itinerary.length
    · refine ⟨r.realization.2.parameter j.succ - 1, by linarith, fun i hi => ?_⟩
      have he := congrArg Fin.val hj
      simp only [Fin.val_succ, Fin.val_last] at he
      have := i.isLt
      have hval : j.val < i.val := hi
      omega
    · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hj
      have hji : j.succ < i.succ := by
        rw [← hi]
        exact Fin.castSucc_lt_succ
      obtain ⟨t, hlow, hupp⟩ := exists_between (r.realization.2.strictAnti_parameter hji)
      refine ⟨t, hupp, fun l hl => lt_of_le_of_lt ?_ hlow⟩
      apply r.realization.2.strictAnti_parameter.antitone
      have he := congrArg Fin.val hi
      simp only [Fin.val_succ, Fin.val_castSucc] at he
      simp only [Fin.le_def, Fin.val_succ]
      have hval : j.val < l.val := hl
      omega
  obtain ⟨t, hu, hl⟩ := cut
  obtain ⟨l, hlt, b, hw, hr, ha, hd⟩ :=
    r.exists_cutoff_truncate_lt j t hu hl (r.lastChangeIndex_spec hq).1
  exact ⟨t, hu, l, hlt, b, hw, hr, ha, hd⟩

end CutoffDecoratedRay

end Mei
