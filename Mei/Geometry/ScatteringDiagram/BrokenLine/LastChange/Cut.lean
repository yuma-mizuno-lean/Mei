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

For every sufficiently small positive displacement before the last degree change,
`CutoffDecoratedRay.eventually_exists_lastChange_incoming` gives an incoming ray
at one lower cutoff. Its endpoint lies on the straight incoming germ, and its
whole incoming decoration, encounter suffix and entire incoming path are retained.
This includes changes with unchanged spatial velocity and later unchanged-degree
encounters.

We use `CutoffDecoratedRay.exists_cutoff_truncate_lt` to retain the encounter
suffix at its intrinsic cutoff, then `PositiveDegrees.cutoff_mono` to place it
at one lower cutoff. The affine segment formula
`Convex.AdmissibleRayRealization.ray_eq_add_smul_of_before_parameter` identifies
the endpoint on the incoming germ.
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
  have hsmall : ∀ᶠ η : ℝ in 𝓝 0, ∀ i : Fin (r.itinerary.length + 1),
      j.succ < i → r.realization.2.parameter i < r.realization.2.parameter j.succ - η := by
    apply eventually_all.mpr
    intro i
    by_cases hi : j.succ < i
    · have hgap := r.realization.2.strictAnti_parameter hi
      filter_upwards [eventually_lt_nhds (sub_pos.mpr hgap)] with η hη _
      linarith
    · exact Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with η hη hpos
  have hpos : 0 < η := Set.mem_Ioi.mp hpos
  let t := r.realization.2.parameter j.succ - η
  have hu : t < r.realization.2.parameter j.succ := sub_lt_self _ hpos
  obtain ⟨l, hlt, b, hw, hr, ha, hp, hd⟩ := r.exists_cutoff_truncate_lt j t hu
    (fun i hi => hη i.succ (Fin.succ_lt_succ_iff.mpr hi)) (r.lastChangeIndex_spec hq).1
  have hfinal : r.realization.1.val j = r.finalDegree := by
    simpa only [Fin.snoc_castSucc] using (r.lastChangeIndex_spec hq).2 j.castSucc le_rfl
  have hbound := (d.mem_cutoff.mp (r.degree_mem j)).2
  rw [hfinal] at hbound
  have hle : l ≤ k - 1 := by omega
  let s : CutoffDecoratedRay d ℳ T a v f c ε P W S C (k - 1) (r.realization.2.ray t) :=
    ⟨b.itinerary, b.realization, fun i => d.cutoff_mono hle (b.degree_mem i), b.degree_sub_mem⟩
  have hx := r.realization.2.ray_eq_add_smul_of_before_parameter j.succ hu.le
    (fun i hi => (hη i hi).le)
  have ht : r.realization.2.ray t =
      r.realization.2.ray (r.realization.2.parameter j.succ) +
        η • v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ) := by
    simpa only [t, sub_sub_cancel] using hx
  rw [← ht]
  refine ⟨s, hw, ?_, ?_, ?_, fun u hu => ?_⟩
  · simpa only [finalDegree_def] using hp
  · simpa only [decoration_eq] using ha
  · simpa only [degreeItinerary_eq] using hd
  · -- `s` reuses `b.realization`; only the cutoff proof fields have changed.
    change b.realization.2.ray u = _
    rw [hr, FiniteAffineRay.truncate_apply _ _ hu]

end CutoffDecoratedRay

end Mei
