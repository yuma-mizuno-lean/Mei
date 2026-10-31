/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut

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

We use `DecoratedAdmissibleRay.truncate`,
`CutoffDecoratedRay.exists_cutoff_truncate` and
`CutoffDecoratedRay.lastChangeIndex_localization` to retain the encounter suffix.
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

private theorem lastChange_incoming_degree_bound (r : Rays) (hq : r.finalDegree ≠ 0)
    (i : Fin r.itinerary.length) (hi : (r.lastChangeIndex hq).val + 1 ≤ i.val) :
    r.realization.1.val i ∈ d.cutoff (k - 1) := by
  let j := r.lastChangeIndex hq
  have hnext : j.val + 1 < r.itinerary.length := lt_of_le_of_lt hi i.isLt
  let next : Fin r.itinerary.length := ⟨j.val + 1, hnext⟩
  have hfinal : r.realization.1.val j = r.finalDegree := by
    simpa only [Fin.snoc_castSucc] using (r.lastChangeIndex_spec hq).2 j.castSucc le_rfl
  have hin : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ =
      r.realization.1.val next := by
    have he : j.succ = next.castSucc := Fin.ext rfl
    rw [he, Fin.snoc_castSucc]
  obtain ⟨-, -, -, -, -, -, hinc⟩ := r.lastChangeIndex_localization hq
  rw [hin] at hinc
  have hmono := d.degree_nonneg (r.degree_sub_mem next i hi)
  have hbound := (d.mem_cutoff.mp (r.degree_mem j)).2
  rw [hfinal] at hbound
  have hmem := (d.mem_cutoff.mp (r.degree_mem i)).1
  simp only [map_sub] at hmono
  exact d.mem_cutoff.mpr ⟨hmem, by omega⟩

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
  have hl : ∀ i : Fin (r.itinerary.length + 1),
      j.val + 1 < i.val → r.realization.2.parameter i < t := fun i hi => hη i hi
  obtain ⟨s, hw, hp, ha, hr⟩ := exists_cutoff_truncate r.itinerary.get r.realization
    (j.val + 1) (r.itinerary.length - (j.val + 1)) (k - 1) (by omega) t hu hl
    (r.lastChange_incoming_degree_bound hq) r.degree_sub_mem
  have hx := r.realization.2.ray_eq_add_smul_of_before_parameter j.succ hu.le
    (fun i hi => (hη i hi).le)
  have ht : r.realization.2.ray t =
      r.realization.2.ray (r.realization.2.parameter j.succ) +
        η • v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ) := by
    simpa only [t, sub_sub_cancel] using hx
  rw [← ht]
  exact ⟨s, by simpa only [List.ofFn_get] using hw, hp, ha, hr⟩

end CutoffDecoratedRay

end Mei
