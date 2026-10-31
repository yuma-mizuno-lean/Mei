/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Straight

/-!
# Straight terminal attachment across all cutoff itineraries

Attach a prescribed unchanged-degree terminal encounter block to every incoming
cutoff ray of a given final degree. The embedding retains the complete older
degree-labelled word and whole decoration. It allows older words of different
lengths, including the empty word, without identifying equal weights.

The weighted image equals the full incoming homogeneous evaluation component.
A predicate on the older degree-labelled word can retain a preceding changing
encounter when removing the later unchanged block in a last-change recursion.
The image criterion requires an actual admitted incoming ray; in particular it
retains the incoming source and all wall and singular avoidance conditions.
It makes no assertion that arbitrary outgoing rays admit a fixed incoming cut.

We use `DecoratedAdmissibleRay.extendStraight`,
`CutoffDecoratedRay.exists_of_word`, uniqueness from the degree-labelled word,
and Mathlib's `Fintype.sum_of_injective`. This is the unchanged-terminal-block
part of the recursion in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k m : ℕ}
  (word : Fin m → J) (q : Γ) (Y : V)
  (hT : ∀ j x, x ∈ ℳ q → (DirectSum.decompose ℳ (T (word j) x) q : M) = x)
  (L : ℝ) (hL : 0 ≤ L) (τ : Fin m → ℝ)
  (hτ : StrictAnti τ) (hpos : ∀ j, 0 < τ j) (hlt : ∀ j, τ j < L)
  (htrans : ∀ j, f (word j) (v q) ≠ 0)
  (hsign : ∀ j, SignType.sign (f (word j) (v q)) = ε (word j))
  (hheight : ∀ j, f (word j) (Y - τ j • v q) = c (word j))
  (hinc : ∀ j, Y - τ j • v q ∈ P (word j))
  (hW : ∀ j u, 0 < u → u ≤ L → (∀ i, u ≠ τ i) → Y - u • v q ∉ W j)
  (hS : ∀ j u, 0 < u → u ≤ L → Y - u • v q ∉ S j)

local notation "In" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Y
local notation "Out" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Y - L • v q)
local notation "A" => {r : In // CutoffDecoratedRay.finalDegree r = q}
local notation "block" => List.ofFn (fun j => (q, word j))

include hT hL hτ hpos hlt htrans hsign hheight hinc hW hS

private theorem exists_straightTerminal (r : A) :
    ∃ z : Out, z.degreeItinerary = block ++ r.val.degreeItinerary ∧
      z.finalDegree = q ∧ z.decoration = r.val.decoration ∧
      z.realization.2.ray = r.val.realization.2.ray.truncate L := by
  have hq : Fin.snoc (α := fun _ => Γ) r.val.realization.1.val 0 0 = q :=
    r.val.finalDegree_def.symm.trans r.property
  let z := r.val.realization.extendStraight (fun j => T (word j))
    (by
      intro j x hx
      rw [hq]
      exact hT j x (by simpa only [hq] using hx)) L hL τ hτ hpos hlt
    (fun j => f (word j)) (fun j => c (word j)) (fun j => P (word j))
    (by simpa only [hq] using htrans)
    (by simpa only [hq] using hheight)
    (by simpa only [hq] using hinc)
    (by simpa only [hq] using hW)
    (by simpa only [hq] using hS)
  have hh : z.1.val = Fin.append (fun _ : Fin m => q) r.val.realization.1.val := by
    simp only [z, DecoratedAdmissibleRay.history_extendStraight, hq]
  let pp := Fin.append (fun _ : Fin m => q) r.val.realization.1.val
  let hz : DecoratedAdmissibleRay ℳ
      (fun j => T (Fin.append word r.val.itinerary.get j)) 0 a v
      (fun j => f (Fin.append word r.val.itinerary.get j))
      (fun j => c (Fin.append word r.val.itinerary.get j))
      (fun j => ε (Fin.append word r.val.itinerary.get j))
      (fun j => P (Fin.append word r.val.itinerary.get j)) W S C (Y - L • v q) := by
    -- Keep the history explicit while transporting only its laws and geometry.
    refine ⟨⟨pp, ?_⟩, ?_⟩
    · have hp := z.1.property
      rw [hh] at hp
      simpa only [← Function.comp_def, Fin.comp_append, hq, hsign] using hp
    · have hp := z.2
      rw [hh] at hp
      simpa only [← Function.comp_def, Fin.comp_append, hq] using hp
  have hhist : hz.1.val = Fin.append (fun _ : Fin m => q) r.val.realization.1.val := rfl
  have hmem : ∀ j, hz.1.val j ∈ d.cutoff k := by
    rw [hhist]
    intro j
    refine Fin.addCases (fun _ => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left, ← r.property] using r.val.finalDegree_mem_cutoff
    · simpa only [Fin.append_right] using r.val.degree_mem j
  have hsub : ∀ i j, i ≤ j → hz.1.val i - hz.1.val j ∈ d.monoid := by
    rw [hhist]
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun _ _ => by simp) (fun j _ => ?_) j
      simp only [Fin.append_left, Fin.append_right]
      let z₀ : Fin r.val.itinerary.length := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
      have hf : r.val.finalDegree = r.val.realization.1.val z₀ := by
        have hi : z₀.castSucc = (0 : Fin (r.val.itinerary.length + 1)) := Fin.ext rfl
        rw [finalDegree_def, ← hi, Fin.snoc_castSucc]
      simpa only [← hf, r.property] using
        r.val.degree_sub_mem z₀ j (by simp [z₀, Fin.le_def])
    · refine Fin.addCases (fun j hij => ?_) (fun j hij => ?_) j
      · have := hij
        simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      · simp only [Fin.append_right]
        exact r.val.degree_sub_mem i j (by simpa only [Fin.le_def,
          Fin.val_natAdd, Nat.add_le_add_iff_left] using hij)
  obtain ⟨b, _, hpath, hdec, hdegree, hword, _⟩ :=
    CutoffDecoratedRay.exists_of_word (Fin.append word r.val.itinerary.get) hz hmem hsub
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · rw [hword, hhist, degreeItinerary_eq, ← List.ofFn_fin_append]
    congr 1
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp
  · rw [hdegree, hhist, ← Fin.append_snoc]
    by_cases hm : m = 0
    · subst m
      simpa only [Fin.append_left_nil _ _ rfl, Function.comp_apply,
        Fin.cast_zero, ← finalDegree_def] using r.property
    · have hzero : (0 : Fin (m + (r.val.itinerary.length + 1))) =
          Fin.castAdd (r.val.itinerary.length + 1) ⟨0, Nat.pos_of_ne_zero hm⟩ := Fin.ext rfl
      rw [hzero, Fin.append_left]
  · rw [hdec, DecoratedAdmissibleRay.decoration_zero, hhist]
    simp only [← Function.comp_def, Fin.comp_append, homogeneousHistory_append,
      LinearMap.comp_apply]
    rw [homogeneousHistory_const_of_decompose_self (T := T ∘ word) hT]
    · exact r.val.decoration_eq.symm
    · simpa only [decoration_eq, Function.comp_def, r.property] using r.val.decoration_mem
  · rw [hpath, ← DecoratedAdmissibleRay.ray_extendStraight
      r.val.realization (fun j => T (word j))
      (by
        intro j x hx
        rw [hq]
        exact hT j x (by simpa only [hq] using hx)) L hL τ hτ hpos hlt
      (fun j => f (word j)) (fun j => c (word j)) (fun j => P (word j))
      (by simpa only [hq] using htrans) (by simpa only [hq] using hheight)
      (by simpa only [hq] using hinc) (by simpa only [hq] using hW)
      (by simpa only [hq] using hS)]
    simp only [hz, eq_mpr_eq_cast, eq_mp_eq_cast, cast_cast]
    -- Index transport leaves the underlying geometric ray unchanged.
    congr 1 <;> simp only [← Function.comp_def, Fin.comp_append,
      z, DecoratedAdmissibleRay.history_extendStraight, hq, pp, cast_heq]

/-- Attach a complete unchanged terminal block to every incoming cutoff ray
of final degree `q`. Older words may have arbitrary lengths; the original source,
all obstacles and every whole decoration are retained. -/
def straightTerminalEmbedding : A ↪ Out where
  toFun r := (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS r).choose
  inj' := by
    intro r s he
    apply Subtype.ext
    apply degreeItinerary_injective
    have hr := (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r).choose_spec.1
    have hs := (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS s).choose_spec.1
    exact List.append_cancel_left (hr.symm.trans ((congrArg degreeItinerary he).trans hs))

/-- Attachment prepends the prescribed block with degree `q` at each encounter,
and retains the complete older degree-labelled itinerary. -/
@[simp]
theorem degreeItinerary_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r).degreeItinerary = block ++ r.val.degreeItinerary :=
  (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS r).choose_spec.1

/-- The final degree remains `q`, including for an empty attached block. -/
@[simp]
theorem finalDegree_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r).finalDegree = q :=
  (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS r).choose_spec.2.1

/-- Every attached encounter preserves the whole incoming final decoration. -/
@[simp↓]
theorem decoration_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r).decoration = r.val.decoration :=
  (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS r).choose_spec.2.2.1

/-- The entire path is continued by endpoint translation, with no new bends. -/
@[simp]
theorem ray_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r).realization.2.ray = r.val.realization.2.ray.truncate L :=
  (exists_straightTerminal word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS r).choose_spec.2.2.2

/-- An outgoing ray is the attachment of a given incoming ray exactly when
its degree-labelled word is the prescribed block followed by that incoming word.
The endpoint and word determine the whole decorated realization. -/
theorem straightTerminalEmbedding_eq_iff (r : A) (z : Out) :
    straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
      hheight hinc hW hS r = z ↔ z.degreeItinerary = block ++ r.val.degreeItinerary := by
  constructor
  · rintro rfl
    exact degreeItinerary_straightTerminalEmbedding ..
  · intro h
    apply degreeItinerary_injective
    rw [degreeItinerary_straightTerminalEmbedding, h]

open Classical in
/-- Sum a selected exact attachment image across all earlier encounter words.
The selection can retain a preceding degree change. Distinct incoming histories
remain distinct even if their weights agree or cancel. -/
theorem sum_ite_decoration_straightTerminal_eq_sum [Finite J]
    (B : List (Γ × J) → Prop) :
    (let := Fintype.ofFinite Out
     ∑ z : Out, if (∃ r : A,
       z.degreeItinerary = block ++ r.val.degreeItinerary ∧ B r.val.degreeItinerary)
       then z.decoration else 0) =
    (let := Fintype.ofFinite A
     ∑ r : A, if B r.val.degreeItinerary then r.val.decoration else 0) := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite Out
  let e : A ↪ Out := straightTerminalEmbedding word q Y hT L hL τ hτ hpos hlt htrans hsign
    hheight hinc hW hS
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro z hz
    rw [ite_eq_right]
    rintro ⟨r, hr, _⟩
    exact hz ⟨r, (straightTerminalEmbedding_eq_iff ..).mpr hr⟩
  · intro r
    have he : ∀ s : A, (e r).degreeItinerary = block ++ s.val.degreeItinerary ↔ s = r := by
      intro s
      rw [← straightTerminalEmbedding_eq_iff word q Y hT L hL τ hτ hpos hlt
        htrans hsign hheight hinc hW hS]
      exact ⟨fun h => e.injective h, fun h => congrArg e h⟩
    simp only [he, exists_eq_left, e, decoration_straightTerminalEmbedding]

open Classical in
/-- The entire weighted attachment image equals the incoming degree-`q`
component of the full cutoff evaluation. This includes all older encounter words
and keeps their actual geometric admission conditions. -/
theorem sum_ite_decoration_straightTerminal_eq_component [Finite J] :
    (let := Fintype.ofFinite Out
     ∑ z : Out, if (∃ r : A, z.degreeItinerary = block ++ r.val.degreeItinerary)
       then z.decoration else 0) =
      (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Y) q : M) := by
  have h := sum_ite_decoration_straightTerminal_eq_sum (d := d) (a := a) (C := C) (k := k)
    word q Y hT L hL τ hτ hpos hlt htrans hsign hheight hinc hW hS (fun _ => True)
  simpa only [and_true, ite_true, ← decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree] using h

end Mei.CutoffDecoratedRay
