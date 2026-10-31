/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cut
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cut.Incoming
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cutoff
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization

/-!
# Incoming cuts at the canonical last degree change

Combine `CutoffDecoratedRay.lastChangeIndex_spec` with the generic incoming-cut
construction to obtain the smaller-cutoff incoming piece of the last-change
recursion in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).

For every sufficiently small positive displacement before the last degree change,
`CutoffDecoratedRay.eventually_exists_lastChange_incoming` gives an incoming ray
at one lower cutoff. Its endpoint lies on the straight incoming germ, and its
whole incoming decoration, encounter suffix and entire incoming path are retained.
This includes changes with unchanged spatial velocity and later unchanged-degree
encounters.

We use `CutoffDecoratedRay.exists_cutoff_truncate_lt` to retain the encounter
suffix at its intrinsic cutoff, and
`CutoffDecoratedRay.eventually_exists_incoming_truncate` for uniform cuts.
Positivity of degree increments places the incoming ray at one lower cutoff;
the general cut already identifies its endpoint on the incoming germ.
-/

public noncomputable section

open Mei.Convex Set Filter
open scoped Topology

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
  obtain ⟨l, hlt, b, hw, hr, ha, hd, _⟩ :=
    r.exists_cutoff_truncate_lt j t hu hl (r.lastChangeIndex_spec hq).1
  exact ⟨t, hu, l, hlt, b, hw, hr, ha, hd⟩

local notation "Rays" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q

/-- Immediately before the last degree change, the entire incoming piece is an
actual ray at one lower cutoff. Retain its whole incoming decoration, all earlier
encounters and the full incoming path. The endpoint is on the straight incoming
germ; no genericity or nonzero spatial change is required. The lower cutoff is
on the degree inventory, with the same coefficient module and propagation maps. -/
theorem eventually_exists_lastChange_incoming (r : Rays) (hq : r.finalDegree ≠ 0) :
    let j := r.lastChangeIndex hq
    let p := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ
    let x := r.realization.2.ray (r.realization.2.parameter j.succ)
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∃ s : CutoffDecoratedRay d ℳ T a v f c ε P W S C (k - 1) (x + η • v p),
        s.itinerary = r.itinerary.drop (j.val + 1) ∧
        s.finalDegree = p ∧ s.decoration = r.realization.decoration j.succ ∧
        s.degreeItinerary = r.degreeItinerary.drop (j.val + 1) ∧
        ∀ u ≤ 0, s.realization.2.ray u =
          r.realization.2.ray (u + (r.realization.2.parameter j.succ - η)) := by
  dsimp only
  let j := r.lastChangeIndex hq
  filter_upwards [r.eventually_exists_incoming_truncate j.succ] with η hη
  obtain ⟨b, hw, hp, ha, hd, hr⟩ := hη
  -- The general cut keeps the original cutoff. At a genuine degree change,
  -- positivity bounds its complete incoming history by one lower cutoff.
  have hlt := r.degree_lt_finalDegree_of_ne j (r.lastChangeIndex_spec hq).1
  have hbound := (d.mem_cutoff.mp r.finalDegree_mem_cutoff).2
  have hin : d.degree b.finalDegree ≤ (k - 1 : ℕ) := by
    rw [hp]
    omega
  let s : CutoffDecoratedRay d ℳ T a v f c ε P W S C (k - 1)
      (r.realization.2.ray (r.realization.2.parameter j.succ) +
        η • v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ)) :=
    b.ofCutoff fun i => d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp (b.degree_mem i)).1,
      (b.degree_le_finalDegree i).trans hin⟩
  -- Only the degree-bound proof fields change; the entire realization is reused.
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [s, ofCutoff_itinerary, Fin.val_succ] using hw
  · simpa only [s, ofCutoff_finalDegree] using hp
  · simpa only [s, ofCutoff_decoration] using ha
  · simpa only [s, ofCutoff_degreeItinerary, Fin.val_succ] using hd
  · simpa only [s, ofCutoff_ray] using hr

end CutoffDecoratedRay

end Mei
