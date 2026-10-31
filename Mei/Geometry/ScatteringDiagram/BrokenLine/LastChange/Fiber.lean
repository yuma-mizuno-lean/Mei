/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Itinerary
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Cut

/-!
# Injectivity of incoming data at the last degree change

For a fixed endpoint, final degree and last changing event, the complete
degree-labelled incoming encounter word determines the entire decorated ray.
In particular, cutting at the last change cannot identify two distinct outgoing
rays even when their encounter words have different lengths. Unchanged terminal
encounters are recovered rather than erased, and a change of degree with equal
spatial velocity remains a change.

The incoming word records every earlier encounter and its selected degree; its
whole decorations are determined by the fixed propagation maps and input. We
give an embedding of the outgoing fiber into these words. A common sufficiently
short cut also embeds it into actual incoming rays at one lower cutoff, indexed
by the changing event and incoming degree, preserving their entire words and
whole incoming decorations. Existence of extensions is a separate geometric question.

We use `CutoffDecoratedRay.itinerary_take_lastChangeIndex_eq`, uniqueness of
admissible backward realizations and Mathlib's list take/drop APIs.
This is the uniqueness part of the last-change recursion in Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

local notation "Rays" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q

/-- The complete incoming degree-labelled encounter word before the last
degree change. The changing encounter and all later unchanged encounters are
removed. The empty word denotes the original incoming tail of degree zero. -/
def lastChangeIncomingItinerary (r : Rays) (hq : r.finalDegree ≠ 0) : List (Γ × J) :=
  r.degreeItinerary.drop ((r.lastChangeIndex hq).val + 1)

/-- Incoming data retain exactly the older degree-labelled encounters. -/
theorem lastChangeIncomingItinerary_def (r : Rays) (hq : r.finalDegree ≠ 0) :
    r.lastChangeIncomingItinerary hq =
      r.degreeItinerary.drop ((r.lastChangeIndex hq).val + 1) := (rfl)

/-- Reconstruct the full degree-labelled word from the terminal word and its
incoming data. No hypothesis on diagonal propagation is used. -/
theorem degreeItinerary_eq_append_lastChangeIncomingItinerary
    (r : Rays) (hq : r.finalDegree ≠ 0) :
    r.degreeItinerary =
      (r.itinerary.take ((r.lastChangeIndex hq).val + 1)).map
        (fun w => (r.finalDegree, w)) ++ r.lastChangeIncomingItinerary hq := by
  rw [lastChangeIncomingItinerary_def, ← degreeItinerary_take_lastChangeIndex_eq]
  exact (List.take_append_drop _ _).symm

/-- At a fixed endpoint and final degree, incoming degree-labelled words and
the last changing label distinguish outgoing rays across all encounter words.
Signed separation is needed only on the common terminal straight half-line. -/
theorem eq_of_lastChangeIncomingItinerary_eq
    (r s : Rays) (hr : r.finalDegree ≠ 0) (hq : r.finalDegree = s.finalDegree)
    (hw : r.itinerary.get (r.lastChangeIndex hr) =
      s.itinerary.get (s.lastChangeIndex (hq ▸ hr)))
    (hin : r.lastChangeIncomingItinerary hr = s.lastChangeIncomingItinerary (hq ▸ hr))
    (hP : ∀ w, P w ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ w w',
      Q - t • v r.finalDegree ∈ P w → Q - t • v r.finalDegree ∈ P w' →
      SignType.sign (f w (v r.finalDegree)) = ε w →
      SignType.sign (f w' (v r.finalDegree)) = ε w' → w = w') : r = s := by
  apply degreeItinerary_injective
  rw [r.degreeItinerary_eq_append_lastChangeIncomingItinerary hr,
    s.degreeItinerary_eq_append_lastChangeIncomingItinerary (hq ▸ hr),
    r.itinerary_take_lastChangeIndex_eq s hr hq hw hP hsep, hin]
  simp only [hq]

section WallEvents

variable {ι : Type*} {T : WallEvent ι → Module.End R M}
  {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}

local notation "P" => fun e : WallEvent ι => WallEvent.support e W
local notation "ν" => fun e : WallEvent ι => WallEvent.normal e f
local notation "b" => fun e : WallEvent ι => WallEvent.offset e c
local notation "ε" => fun e : WallEvent ι => Prod.snd e
local notation "EventRays" => CutoffDecoratedRay d ℳ T a v ν b ε P P S C k Q

/-- Exact incidence and the normal sign distinguish canonical simultaneous
events, so equality of the incoming data and last changing event recovers the
whole ray without an additional label-separation assumption. -/
theorem eq_of_lastChangeIncomingItinerary_eq_wallEvents
    (r s : EventRays) (hr : r.finalDegree ≠ 0) (hq : r.finalDegree = s.finalDegree)
    (hw : r.itinerary.get (r.lastChangeIndex hr) =
      s.itinerary.get (s.lastChangeIndex (hq ▸ hr)))
    (hin : r.lastChangeIncomingItinerary hr = s.lastChangeIncomingItinerary (hq ▸ hr)) :
    r = s := by
  apply r.eq_of_lastChangeIncomingItinerary_eq s hr hq hw hin
    (fun e => subset_iUnion P e)
  intro t _ e e' he he' hs hs'
  exact e.eq_of_mem_support_of_normal_sign_eq e' W f (v r.finalDegree) he he' hs hs'

/-- Last-change incoming data embed a fixed nonzero-final-degree fiber into
pairs consisting of the changing event and the entire earlier decorated word.
All encounter lengths are allowed; no finite-alphabet hypothesis is needed. -/
def lastChangeIncomingEmbedding (q : Γ) (hq : q ≠ 0) :
    {r : EventRays // r.finalDegree = q} ↪ WallEvent ι × List (Γ × WallEvent ι) where
  toFun r := (r.val.itinerary.get (r.val.lastChangeIndex (r.property.symm ▸ hq)),
    r.val.lastChangeIncomingItinerary (r.property.symm ▸ hq))
  inj' := by
    intro r s h
    apply Subtype.ext
    exact r.val.eq_of_lastChangeIncomingItinerary_eq_wallEvents s.val
      (r.property.symm ▸ hq) (r.property.trans s.property.symm)
      (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The last-change embedding records precisely the changing event and older
degree-labelled encounter word. -/
@[simp]
theorem lastChangeIncomingEmbedding_apply (q : Γ) (hq : q ≠ 0)
    (r : {r : EventRays // r.finalDegree = q}) :
    lastChangeIncomingEmbedding q hq r =
      (r.val.itinerary.get (r.val.lastChangeIndex (r.property.symm ▸ hq)),
        r.val.lastChangeIncomingItinerary (r.property.symm ▸ hq)) := (rfl)

open Classical in
/-- One sufficiently small displacement cuts every outgoing ray of final degree
`q` into actual incoming rays at one lower cutoff, injectively across all encounter
words. The target remembers the changing event and incoming degree, which fix its
endpoint. Every older encounter and the whole coefficient entering the last change
are preserved. Later unchanged encounters need not be absent. -/
theorem eventually_exists_lastChangeIncomingEmbedding [Finite ι]
    (q : Γ) (hq : q ≠ 0) :
    let F := {r : EventRays // r.finalDegree = q}
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∃ e : F ↪ (Σ w : WallEvent ι, Σ p : Γ,
        CutoffDecoratedRay d ℳ T a v ν b ε P P S C (k - 1)
          (Q + ((b w - ν w Q) / ν w (v q)) • v q + η • v p)),
        ∀ r : F,
          (e r).1 = r.val.itinerary.get (r.val.lastChangeIndex (r.property.symm ▸ hq)) ∧
          (e r).2.1 = Fin.snoc (α := fun _ => Γ) r.val.realization.1.val 0
            (r.val.lastChangeIndex (r.property.symm ▸ hq)).succ ∧
          (e r).2.2.finalDegree = (e r).2.1 ∧
          (e r).2.2.degreeItinerary = r.val.lastChangeIncomingItinerary
            (r.property.symm ▸ hq) ∧
          (e r).2.2.decoration = r.val.realization.decoration
            (r.val.lastChangeIndex (r.property.symm ▸ hq)).succ := by
  classical
  dsimp only
  let F := {r : EventRays // r.finalDegree = q}
  let index (r : F) := r.val.lastChangeIndex (r.property.symm ▸ hq)
  let wall (r : F) := r.val.itinerary.get (index r)
  let degree (r : F) := Fin.snoc (α := fun _ => Γ) r.val.realization.1.val 0 (index r).succ
  let Incoming (η : ℝ) (w : WallEvent ι) (p : Γ) :=
    CutoffDecoratedRay d ℳ T a v ν b ε P P S C (k - 1)
      (Q + ((b w - ν w Q) / ν w (v q)) • v q + η • v p)
  have hcuts : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ r : F,
      ∃ s : Incoming η (wall r) (degree r),
        s.finalDegree = degree r ∧
        s.degreeItinerary = r.val.lastChangeIncomingItinerary (r.property.symm ▸ hq) ∧
        s.decoration = r.val.realization.decoration (index r).succ := by
    apply eventually_all.mpr
    intro r
    filter_upwards [r.val.eventually_exists_lastChange_incoming (r.property.symm ▸ hq)]
      with η hη
    obtain ⟨-, -, -, hx, -⟩ :=
      r.val.lastChangeIndex_localization (r.property.symm ▸ hq)
    have hpoint : r.val.realization.2.ray (r.val.realization.2.parameter (index r).succ) =
        Q + ((b (wall r) - ν (wall r) Q) / ν (wall r) (v q)) • v q := by
      simpa only [r.property] using hx
    obtain ⟨s, _, hp, hd, hi, _⟩ := hη
    have hs : ∃ s : CutoffDecoratedRay d ℳ T a v ν b ε P P S C (k - 1)
        (r.val.realization.2.ray (r.val.realization.2.parameter (index r).succ) +
          η • v (degree r)),
        s.finalDegree = degree r ∧
        s.degreeItinerary = r.val.lastChangeIncomingItinerary (r.property.symm ▸ hq) ∧
        s.decoration = r.val.realization.decoration (index r).succ :=
      ⟨s, hp, hi, hd⟩
    rw [hpoint] at hs
    exact hs
  filter_upwards [hcuts] with η hη
  choose s hdegree hword hdecoration using hη
  let g (r : F) : Σ w, Σ p, Incoming η w p := ⟨wall r, degree r, s r⟩
  have hg : Function.Injective g := by
    intro r r' he
    apply (lastChangeIncomingEmbedding q hq).injective
    apply Prod.ext
    · exact congrArg Sigma.fst he
    · have hi := congrArg (fun z : Σ w, Σ p, Incoming η w p => z.2.2.degreeItinerary) he
      exact (hword r).symm.trans (hi.trans (hword r'))
  exact ⟨⟨g, hg⟩, fun r => ⟨rfl, rfl, hdegree r, hword r, hdecoration r⟩⟩

end WallEvents

end Mei.CutoffDecoratedRay
