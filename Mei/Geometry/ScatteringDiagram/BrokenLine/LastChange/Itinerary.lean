/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization
public import Mei.Geometry.Convex.Sweep.Admissible.Itinerary
public import Mei.Geometry.Convex.Polyhedron.WallEvent

/-!
# Recovering the terminal word at the last degree change

Two decorated rays with the same endpoint, final degree and last changing wall
have the same complete terminal encounter word, including unchanged-degree
encounters. Their incoming histories may differ. This removes the apparent
choice of a terminal word when regrouping weighted rays by their last change.
Changes of degree with unchanged spatial velocity remain recorded.

We combine `CutoffDecoratedRay.lastChangeIndex_localization`, the straight
terminal path formula and `AdmissibleRayRealization.encounterParameters_take_eq_of_ray_eqOn`.
Signed separation identifies the labels from their common encounter positions;
canonical signed simultaneous wall events satisfy this condition.
The last-change recursion follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

/-- The last changing wall and final degree determine the complete terminal
encounter word, read backwards from the endpoint and including that change.
Every encounter lies on an obstacle; signed separation distinguishes labels at
each point of the terminal straight ray. No diagonal propagation, consistency,
nonzero spatial velocity or genericity hypothesis is required. -/
theorem itinerary_take_lastChangeIndex_eq
    (r s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (hr : r.finalDegree ≠ 0) (hq : r.finalDegree = s.finalDegree)
    (hw : r.itinerary.get (r.lastChangeIndex hr) =
      s.itinerary.get (s.lastChangeIndex (hq ▸ hr)))
    (hP : ∀ w, P w ⊆ ⋃ b, W b)
    (hsep : ∀ t < (0 : ℝ), ∀ w w',
      Q - t • v r.finalDegree ∈ P w → Q - t • v r.finalDegree ∈ P w' →
      SignType.sign (f w (v r.finalDegree)) = ε w →
      SignType.sign (f w' (v r.finalDegree)) = ε w' → w = w') :
    r.itinerary.take ((r.lastChangeIndex hr).val + 1) =
      s.itinerary.take ((s.lastChangeIndex (hq ▸ hr)).val + 1) := by
  let hs : s.finalDegree ≠ 0 := hq ▸ hr
  let j := r.lastChangeIndex hr
  let l := s.lastChangeIndex hs
  have htime : r.realization.2.parameter j.succ = s.realization.2.parameter l.succ := by
    obtain ⟨-, -, ht, -⟩ := r.lastChangeIndex_localization hr
    obtain ⟨-, -, ht', -⟩ := s.lastChangeIndex_localization hs
    rw [ht, ht', hw]
    exact congrArg (fun q => -((c (s.itinerary.get l) - f (s.itinerary.get l) Q) /
      f (s.itinerary.get l) (v q))) hq
  -- Both terminal pieces are the same straight path, even when the last
  -- coefficient change has zero spatial projection.
  have hpath (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
      (hr : r.finalDegree ≠ 0) {t : ℝ}
      (ht : t ∈ Icc (r.realization.2.parameter (r.lastChangeIndex hr).succ) 0) :
      r.realization.2.ray t = Q - t • v r.finalDegree := by
    obtain ⟨-, hp⟩ := r.lastChangeIndex_spec hr
    have h := r.realization.2.ray_eq_endpoint_sub_smul (r.lastChangeIndex hr).succ
      (fun i hi => congrArg v ((hp i (Fin.le_castSucc_iff.mpr hi)).trans r.finalDegree_def)) ht
    simpa only [← r.finalDegree_def] using h
  have ht := r.realization.2.encounterParameters_take_eq_of_ray_eqOn s.realization.2 j l
    htime (fun t ht => by rw [hpath r hr ht, hpath s hs (by simpa only [htime] using ht), hq])
    (fun i _ => hP (r.itinerary.get i)) (fun i _ => hP (s.itinerary.get i))
  have hlength : j.val = l.val := by
    have h := congrArg List.length ht
    simp only [List.length_take, List.length_ofFn,
      Nat.min_eq_left (Nat.succ_le_of_lt j.isLt),
      Nat.min_eq_left (Nat.succ_le_of_lt l.isLt)] at h
    omega
  -- Equal ordered time lists determine their lengths and corresponding indices.
  apply List.ext_get (by rw [List.length_take_of_le (Nat.succ_le_of_lt j.isLt),
    List.length_take_of_le (Nat.succ_le_of_lt l.isLt), hlength])
  intro i hi hi'
  have hir : i < r.itinerary.length := hi.trans_le (List.length_take_le' _ _)
  have his : i < s.itinerary.length := hi'.trans_le (List.length_take_le' _ _)
  let u : Fin r.itinerary.length := ⟨i, hir⟩
  let u' : Fin s.itinerary.length := ⟨i, his⟩
  have hu : u ≤ j := by
    have := List.length_take_le (i := j.val + 1) (l := r.itinerary)
    simpa only [u, Fin.le_def] using Nat.le_of_lt_succ (hi.trans_le this)
  have hu' : u' ≤ l := by
    have := List.length_take_le (i := l.val + 1) (l := s.itinerary)
    simpa only [u', Fin.le_def] using Nat.le_of_lt_succ (hi'.trans_le this)
  have htu : r.realization.2.parameter u.succ = s.realization.2.parameter u'.succ := by
    have h := congrArg (fun ts : List ℝ => ts[i]?) ht
    have hij : i < j.val + 1 := hi.trans_le (List.length_take_le _ _)
    have hil : i < l.val + 1 := hi'.trans_le (List.length_take_le _ _)
    simpa [List.getElem?_take, hij, hil, u, u', hir, his] using h
  have hneg : r.realization.2.parameter u.succ < 0 := by
    simpa only [r.realization.2.parameter_zero] using
      r.realization.2.strictAnti_parameter (Fin.succ_pos u)
  have hdom : r.realization.2.parameter u.succ ∈
      Icc (r.realization.2.parameter j.succ) 0 :=
    ⟨r.realization.2.strictAnti_parameter.antitone (Fin.succ_le_succ_iff.mpr hu), hneg.le⟩
  have hdom' : s.realization.2.parameter u'.succ ∈
      Icc (s.realization.2.parameter l.succ) 0 := by
    simpa only [← htu, ← htime] using hdom
  have hdegree : r.realization.1.val u = r.finalDegree := by
    simpa only [Fin.snoc_castSucc] using (r.lastChangeIndex_spec hr).2 u.castSucc
      (Fin.castSucc_le_castSucc_iff.mpr hu)
  have hdegree' : s.realization.1.val u' = s.finalDegree := by
    simpa only [Fin.snoc_castSucc] using (s.lastChangeIndex_spec hs).2 u'.castSucc
      (Fin.castSucc_le_castSucc_iff.mpr hu')
  -- Signed separation now recovers the actual labels at the matched times.
  have he := hsep _ hneg (r.itinerary.get u) (s.itinerary.get u')
    (by simpa only [hpath r hr hdom] using r.realization.2.incidence u)
    (by
      have h := s.realization.2.incidence u'
      rw [hpath s hs hdom', ← hq, ← htu] at h
      exact h)
    (by simpa only [hdegree] using r.realization.crossing_sign u)
    (by simpa only [hdegree', ← hq] using s.realization.crossing_sign u')
  simpa only [List.getElem_take, List.get_eq_getElem] using he

/-- The terminal degree-labelled block repeats the final degree on the complete
terminal encounter word, including the last change itself. -/
theorem degreeItinerary_take_lastChangeIndex_eq
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) (hq : r.finalDegree ≠ 0) :
    r.degreeItinerary.take ((r.lastChangeIndex hq).val + 1) =
      (r.itinerary.take ((r.lastChangeIndex hq).val + 1)).map
        (fun w => (r.finalDegree, w)) := by
  let j := r.lastChangeIndex hq
  apply List.ext_getElem
  · simp only [List.length_take, length_degreeItinerary, List.length_map]
  · intro i hi hi'
    have hir : i < r.itinerary.length := by
      have h := List.length_take_le' (j.val + 1) r.degreeItinerary
      rw [length_degreeItinerary] at h
      exact hi.trans_le h
    have hij : i ≤ j.val := by
      exact Nat.le_of_lt_succ (hi.trans_le
        (List.length_take_le ((r.lastChangeIndex hq).val + 1) r.degreeItinerary))
    have hd := (r.lastChangeIndex_spec hq).2 (⟨i, hir⟩ : Fin r.itinerary.length).castSucc
      (by simpa only [Fin.le_def, Fin.val_castSucc] using hij)
    simpa only [degreeItinerary_eq, List.getElem_take, List.getElem_map,
      List.getElem_ofFn, List.get_eq_getElem, Fin.snoc_castSucc] using
      congrArg (fun q => (q, r.itinerary[i])) hd

section WallEvents

variable {ι : Type*} {T : WallEvent ι → Module.End R M}
  {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}

local notation "P" => fun e : WallEvent ι => WallEvent.support e W
local notation "ν" => fun e : WallEvent ι => WallEvent.normal e f
local notation "b" => fun e : WallEvent ι => WallEvent.offset e c
local notation "ε" => fun e : WallEvent ι => Prod.snd e

/-- For canonical signed simultaneous events, the final degree and last
changing event alone determine the terminal word. Exact incidence supplies
separation, so no additional hypothesis about labels or propagation is needed.
All indexed coincident walls and later unchanged encounters are retained. -/
theorem itinerary_take_lastChangeIndex_eq_wallEvents
    (r s : CutoffDecoratedRay d ℳ T a v ν b ε P P S C k Q)
    (hr : r.finalDegree ≠ 0) (hq : r.finalDegree = s.finalDegree)
    (hw : r.itinerary.get (r.lastChangeIndex hr) =
      s.itinerary.get (s.lastChangeIndex (hq ▸ hr))) :
    r.itinerary.take ((r.lastChangeIndex hr).val + 1) =
      s.itinerary.take ((s.lastChangeIndex (hq ▸ hr)).val + 1) := by
  apply r.itinerary_take_lastChangeIndex_eq s hr hq hw
    (fun e => subset_iUnion P e)
  intro t _ e e' he he' hs hs'
  exact e.eq_of_mem_support_of_normal_sign_eq e' W f (v r.finalDegree) he he' hs hs'

end WallEvents

end Mei.CutoffDecoratedRay
