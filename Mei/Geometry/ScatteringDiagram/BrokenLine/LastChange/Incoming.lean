/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cut

/-!
# Lower-cutoff incoming rays at the last degree change

Cut a contributing ray immediately before its last positive degree change.
Every retained degree is bounded by the incoming degree at that encounter,
which is strictly smaller than the final degree. The incoming piece therefore
belongs to the full ray family at one lower cutoff, with the original input,
whole incoming decoration, encounter suffix and entire incoming path retained.
Its endpoint is on the straight incoming germ of the selected encounter.

This supplies actual lower-degree rays for a last-change recursion, including
changes with unchanged spatial velocity and later unchanged-degree encounters.
It does not perturb the incoming germ or assert a cut/glue bijection.

We use `CutoffDecoratedRay.exists_cutoff_truncate_lt` to retain the encounter
suffix at its intrinsic cutoff, then `PositiveDegrees.cutoff_mono` to place it
at one lower cutoff. The affine segment formula
`Convex.AdmissibleRayRealization.ray_eq_add_smul_of_before_parameter` identifies
the endpoint on the incoming germ.
The last-change recursion and incoming-germ conventions follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
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
  have hpos : 0 < η := hpos
  let t := r.realization.2.parameter j.succ - η
  have hu : t < r.realization.2.parameter j.succ := sub_lt_self _ hpos
  obtain ⟨l, hlt, b, hw, hr, ha, hp⟩ := r.exists_cutoff_truncate_lt j t hu
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
  refine ⟨s, hw, ?_, ?_, fun u hu => ?_⟩
  · simpa only [finalDegree_def] using hp
  · simpa only [decoration_eq] using ha
  · change b.realization.2.ray u = _
    rw [hr, FiniteAffineRay.truncate_apply _ _ hu]

end CutoffDecoratedRay

end Mei
