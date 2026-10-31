/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.WallEvent

/-!
# Restricting simultaneous wall events

Restrict the incidence set of a simultaneous event along an embedding of wall
indices. If no incident wall remains, the event disappears. Otherwise its sign
is read from the supplied velocity at the newly chosen representative normal;
the old and new representatives may have opposite coorientations.

Restriction preserves exact incidence and regular transverse realizations,
and successive restrictions compose. Neither wall index type needs to be
finite: `Finset.preimage` constructs the finite retained incidence set.
This is the event-level geometry of deleting walls from a diagram, using the
same signed-event convention as `WallEvent`.
-/

public noncomputable section

open Set

namespace Mei.Convex.WallEvent

variable {ι κ η V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Retain the incident indices in the image of `u`, recomputing the sign on
their representative normal using `v`. Return `none` if none remain.
The velocity specifies the new sign, independently of the old recorded sign. -/
def restrict (e : WallEvent ι) (u : κ ↪ ι) (f : κ → V →L[ℝ] ℝ) (v : V) :
    Option (WallEvent κ) :=
  let s := e.1.val.preimage u u.injective.injOn
  if hs : s.Nonempty then some (⟨s, hs⟩, SignType.sign (f hs.choose v)) else none

/-- An event disappears exactly when all its incident indices are omitted. -/
@[simp]
theorem restrict_eq_none_iff (e : WallEvent ι) (u : κ ↪ ι)
    (f : κ → V →L[ℝ] ℝ) (v : V) :
    e.restrict u f v = none ↔ ∀ j, u j ∉ e.1.val := by
  classical
  unfold restrict
  dsimp only
  split_ifs with hs
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, Finset.mem_preimage.mp hj⟩
  · simp only [true_iff]
    exact fun j hj => hs ⟨j, Finset.mem_preimage.mpr hj⟩

/-- A surviving restriction records precisely the retained incident indices,
with the sign of the velocity at its chosen normal. -/
@[simp]
theorem restrict_eq_some_iff (e : WallEvent ι) (u : κ ↪ ι)
    (f : κ → V →L[ℝ] ℝ) (v : V) (e' : WallEvent κ) :
    e.restrict u f v = some e' ↔
      (∀ j, j ∈ e'.1.val ↔ u j ∈ e.1.val) ∧
        SignType.sign (e'.normal f v) = e'.2 := by
  classical
  unfold restrict
  dsimp only
  split_ifs with hs
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨fun _ => by simp only [Finset.mem_preimage], by simp only [normal_def]⟩
    · rintro ⟨hi, hv⟩
      have he : (⟨e.1.val.preimage u u.injective.injOn, hs⟩ :
          {s : Finset κ // s.Nonempty}) = e'.1 := by
        apply Subtype.ext
        apply Finset.ext
        intro j
        simpa only [Finset.mem_preimage] using (hi j).symm
      apply Prod.ext he
      simpa only [normal_def, ← he] using hv
  · simp only [false_iff, not_and]
    intro hi _
    exact (hs ⟨e'.1.property.choose,
      Finset.mem_preimage.mpr ((hi _).mp e'.1.property.choose_spec)⟩).elim

/-- Restriction preserves the exact incidence of every original event point. -/
theorem support_subset_of_restrict_eq_some {e : WallEvent ι} {u : κ ↪ ι}
    {f : κ → V →L[ℝ] ℝ} {v : V} {e' : WallEvent κ}
    (he : e.restrict u f v = some e') (W : ι → Set V) :
    e.support W ⊆ e'.support (W ∘ u) := by
  intro x hx
  rw [mem_support] at hx ⊢
  exact fun j => (hx (u j)).trans (((restrict_eq_some_iff ..).mp he).1 j).symm

/-- If an event disappears, none of its points lies on a retained wall. -/
theorem notMem_iUnion_of_restrict_eq_none {e : WallEvent ι} {u : κ ↪ ι}
    {f : κ → V →L[ℝ] ℝ} {v : V}
    (he : e.restrict u f v = none) (W : ι → Set V) {x : V}
    (hx : x ∈ e.support W) : x ∉ ⋃ j, W (u j) := by
  intro h
  obtain ⟨j, hj⟩ := mem_iUnion.mp h
  exact (restrict_eq_none_iff ..).mp he j (((mem_support ..).mp hx (u j)).mp hj)

/-- Keeping all indices retains the incidence set and recomputes its sign.
Thus it recovers the original event when that sign already agrees with `v`. -/
@[simp]
theorem restrict_refl (e : WallEvent ι) (f : ι → V →L[ℝ] ℝ) (v : V) :
    e.restrict (Function.Embedding.refl ι) f v =
      some (e.1, SignType.sign (e.normal f v)) := by
  exact (restrict_eq_some_iff ..).mpr
    ⟨fun _ => Iff.rfl, by simp only [normal_def]⟩

/-- Successive restrictions retain the same incidence and sign as restriction
along the composite embedding. A disappeared event stays absent. -/
@[simp]
theorem restrict_trans (e : WallEvent ι) (u : κ ↪ ι) (w : η ↪ κ)
    (f : κ → V →L[ℝ] ℝ) (v : V) :
    e.restrict (w.trans u) (f ∘ w) v =
      (e.restrict u f v).bind (fun b => b.restrict w (f ∘ w) v) := by
  apply Option.ext
  intro z
  rw [Option.bind_eq_some_iff]
  constructor
  · intro hz
    obtain ⟨hi, hv⟩ := (restrict_eq_some_iff ..).mp hz
    cases hr : e.restrict u f v with
    | none =>
      exact ((restrict_eq_none_iff ..).mp hr (w z.1.property.choose)
        ((hi _).mp z.1.property.choose_spec)).elim
    | some b =>
      refine ⟨b, rfl, (restrict_eq_some_iff ..).mpr ⟨?_, hv⟩⟩
      intro j
      exact (hi j).trans (((restrict_eq_some_iff ..).mp hr).1 (w j)).symm
  · rintro ⟨b, hb, hz⟩
    obtain ⟨hi, hv⟩ := (restrict_eq_some_iff ..).mp hz
    refine (restrict_eq_some_iff ..).mpr ⟨?_, hv⟩
    exact fun j => (hi j).trans (((restrict_eq_some_iff ..).mp hb).1 (w j))

/-- A surviving restriction is realized at the same point with the same
transverse velocity. Restricting the wall family creates no singular points. -/
theorem isRealizedEvent_of_restrict_eq_some {e : WallEvent ι} {u : κ ↪ ι}
    {f : ι → V →L[ℝ] ℝ} {v x : V} {e' : WallEvent κ} {W : ι → Set V}
    (he : e.restrict u (f ∘ u) v = some e')
    (hx : x ∈ e.support W) (hreg : x ∉ singularSupport W)
    (hv : ∀ j, x ∈ W j → f j v ≠ 0) :
    e'.IsRealizedEvent (W ∘ u) (f ∘ u) := by
  rw [isRealizedEvent_iff]
  refine ⟨⟨x, fun h => hreg (singularSupport_comp_subset W u h)⟩, v,
    support_subset_of_restrict_eq_some he W hx, fun j hj => hv (u j) hj,
    ((restrict_eq_some_iff ..).mp he).2⟩

end Mei.Convex.WallEvent
