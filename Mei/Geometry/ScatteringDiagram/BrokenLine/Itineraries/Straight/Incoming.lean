/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Straight
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut.Incoming
public import Mei.Geometry.Affine.Segment

/-!
# Complete cutoff sums across unchanged terminal blocks

At every sufficiently small straight incoming cut, removing a prescribed nonempty
unchanged-degree terminal encounter block preserves its complete weighted fiber.
The sum includes every older encounter word, retains the original source and all
obstacles, and permits an arbitrary selection on the older degree-labelled history.
Thus a preceding degree-changing encounter can be selected without fixing the
older word. Whole decorations and multiplicities are preserved.

We combine `CutoffDecoratedRay.sum_ite_decoration_straightTerminal_eq_sum` with
`DecoratedAdmissibleRay.eventually_exists_incoming_truncate` and
`eventually_extendSegment_notMem`. This is the unchanged-terminal-block part
of the backward-ray recursion in Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k m : ℕ} {Q : V}

-- This helper is specific to removing a constant-degree prefix: the incoming
-- degree and the whole prescribed block are retained in its conclusion.
private theorem eventually_suffix {n : ℕ} (u : Fin (m + 1 + n) → J)
    (r : DecoratedAdmissibleRay ℳ (fun j => T (u j)) 0 a v
      (fun j => f (u j)) (fun j => c (u j))
      (fun j => ε (u j)) (fun j => P (u j)) W S C Q)
    (hmem : ∀ j, r.1.val j ∈ d.cutoff k)
    (hmono : ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
    (q : Γ) (t : ℝ)
    (hp : ∀ i : Fin (m + 1), r.1.val (Fin.castAdd n i) = q)
    (hb : Fin.snoc (α := fun _ => Γ) r.1.val 0
      (Fin.natAdd (m + 1) (0 : Fin (n + 1))) = q)
    (ht : r.2.parameter (Fin.natAdd (m + 1) (0 : Fin (n + 1))) = -t) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q + (t + η) • v q),
        b.finalDegree = q ∧ b.degreeItinerary =
          List.ofFn (fun j : Fin n => (r.1.val (Fin.natAdd (m + 1) j),
            u (Fin.natAdd (m + 1) j))) := by
  let i := Fin.natAdd (m + 1) (0 : Fin (n + 1))
  have hzero : Fin.snoc (α := fun _ => Γ) r.1.val 0 0 = q := by
    have he : (0 : Fin (m + 1 + n + 1)) =
        (Fin.castAdd n (0 : Fin (m + 1))).castSucc := Fin.ext rfl
    rw [he, Fin.snoc_castSucc, hp]
  have hpoint := r.2.ray_eq_endpoint_sub_smul i
    (fun j hj => by
      have hj' : j.val < m + 1 := by
        have := Fin.lt_def.mp hj
        simp only [i, Fin.val_natAdd, Fin.val_zero, add_zero] at this
        exact this
      have he : j = (Fin.castAdd n (⟨j.val, hj'⟩ : Fin (m + 1))).castSucc := Fin.ext rfl
      rw [he, Fin.snoc_castSucc, hp]
      exact (congrArg v hzero).symm)
    (t := r.2.parameter i)
    ⟨le_rfl, by simpa only [r.2.parameter_zero] using
      r.2.strictAnti_parameter.antitone (Fin.zero_le i)⟩
  rw [hzero, ht, neg_smul, sub_neg_eq_add] at hpoint
  filter_upwards [r.eventually_exists_incoming_truncate (m := m + 1) (n := n)] with η hη
  have he : r.2.ray (r.2.parameter i) + η • v
      (Fin.snoc (α := fun _ => Γ) r.1.val 0 i) = Q + (t + η) • v q := by
    rw [ht, hpoint, hb, add_smul, add_assoc]
  rw [he] at hη
  obtain ⟨s, hh, _, _, _⟩ := hη
  obtain ⟨b, _, _, _, hq, hw, _⟩ := exists_of_word
    (fun j : Fin n => u (Fin.natAdd (m + 1) j)) s
    (fun j => by rw [hh]; exact hmem _)
    (fun j l hjl => by
      rw [hh]
      exact hmono _ _ (by simpa only [Fin.le_def, Fin.val_natAdd,
        Nat.add_le_add_iff_left] using hjl))
  refine ⟨b, ?_, ?_⟩
  · rw [hq, hh]
    exact (congrFun (Fin.snoc_comp_natAdd r.1.val 0) 0).symm.trans hb
  · simpa only [hh] using hw


private theorem eventually_admits_suffix [Finite J]
    (word : Fin (m + 1) → J) (q : Γ) (t : ℝ)
    (htrans : f (word (Fin.last m)) (v q) ≠ 0)
    (hheight : f (word (Fin.last m)) (Q + t • v q) = c (word (Fin.last m))) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∀ z : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        z.degreeItinerary.take (m + 1) = List.ofFn (fun j => (q, word j)) →
        ((z.degreeItinerary.drop (m + 1)).map Prod.fst).headD 0 = q →
        ∃ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q + (t + η) • v q),
          r.finalDegree = q ∧ r.degreeItinerary = z.degreeItinerary.drop (m + 1) := by
  -- Split only the tuple length; retain the actual realization throughout.
  have cut {N : ℕ} (u : Fin N → J)
      (r : DecoratedAdmissibleRay ℳ (fun j => T (u j)) 0 a v
        (fun j => f (u j)) (fun j => c (u j))
        (fun j => ε (u j)) (fun j => P (u j)) W S C Q)
      (hm : ∀ j, r.1.val j ∈ d.cutoff k)
      (hmono : ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
      (hpre : (List.ofFn (fun j => (r.1.val j, u j))).take (m + 1) =
        List.ofFn (fun j => (q, word j)))
      (hb : (((List.ofFn (fun j => (r.1.val j, u j))).drop (m + 1)).map
        Prod.fst).headD 0 = q) :
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C k (Q + (t + η) • v q),
          b.finalDegree = q ∧ b.degreeItinerary =
            (List.ofFn (fun j => (r.1.val j, u j))).drop (m + 1) := by
    have hlen : m + 1 ≤ N := by
      have hh := congrArg List.length hpre
      simp only [List.length_take, List.length_ofFn] at hh
      omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hlen
    rw [List.ofFn_add] at hpre hb ⊢
    simp only [List.length_ofFn, List.take_left', List.drop_left'] at hpre hb ⊢
    have htuple := List.ofFn_injective hpre
    have hp (i : Fin (m + 1)) : r.1.val (Fin.castAdd n i) = q :=
      congrArg Prod.fst (congrFun htuple i)
    have hw (i : Fin (m + 1)) : u (Fin.castAdd n i) = word i :=
      congrArg Prod.snd (congrFun htuple i)
    have hboundary : Fin.snoc (α := fun _ => Γ) r.1.val 0
        (Fin.natAdd (m + 1) (0 : Fin (n + 1))) = q := by
      have he := congrFun (Fin.snoc_comp_natAdd r.1.val 0) 0
      simp only [Function.comp_apply] at he
      rw [he]
      cases n with
      | zero => simpa [Fin.snoc_zero] using hb
      | succ n => simpa [List.ofFn_succ] using hb
    let j := Fin.castAdd n (Fin.last m)
    have hzero : Fin.snoc (α := fun _ => Γ) r.1.val 0 0 = q := by
      have he : (0 : Fin (m + 1 + n + 1)) =
          (Fin.castAdd n (0 : Fin (m + 1))).castSucc := Fin.ext rfl
      rw [he, Fin.snoc_castSucc, hp]
    -- Constant terminal degree identifies the common geometric cut point.
    have htime := r.2.parameter_eq_div_of_directions_eq j (fun i hi => by
      have hi' : i.val < m + 1 := by
        have hi' := Fin.le_iff_val_le_val.mp hi
        simp only [j, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hi'
        omega
      have he : i = (Fin.castAdd n (⟨i.val, hi'⟩ : Fin (m + 1))).castSucc := Fin.ext rfl
      rw [he, Fin.snoc_castSucc, hp, hzero])
    have hj : j.succ = Fin.natAdd (m + 1) (0 : Fin (n + 1)) := by
      ext
      simp [j]
    have hdiv : (f (word (Fin.last m)) Q - c (word (Fin.last m))) /
        f (word (Fin.last m)) (v q) = -t := by
      apply (div_eq_iff htrans).mpr
      rw [map_add, map_smul, smul_eq_mul] at hheight
      linarith
    rw [hj, hzero, hw, hdiv] at htime
    exact eventually_suffix u r hm hmono q t hp hboundary htime
  apply eventually_all.mpr
  intro z
  by_cases hp : z.degreeItinerary.take (m + 1) = List.ofFn (fun j => (q, word j)) ∧
      ((z.degreeItinerary.drop (m + 1)).map Prod.fst).headD 0 = q
  · filter_upwards [cut z.itinerary.get z.realization z.degree_mem z.degree_sub_mem
      (by simpa only [← degreeItinerary_eq] using hp.1)
      (by simpa only [← degreeItinerary_eq] using hp.2)]
      with η hη _ _
    simpa only [← degreeItinerary_eq] using hη
  · exact Eventually.of_forall fun _ h₁ h₂ => (hp ⟨h₁, h₂⟩).elim

open Classical in
/-- Removing a nonempty unchanged terminal block preserves the complete weighted
cutoff fiber at every sufficiently short incoming cut. The outgoing selection
uses only the recorded word and boundary degree; no incoming-admission test
remains. `B` may select a preceding degree change without fixing older words. -/
theorem eventually_sum_straightTerminal_eq_sum [Finite J] [Finite K]
    (word : Fin (m + 1) → J) (q : Γ)
    (hT : ∀ j x, x ∈ ℳ q → (DirectSum.decompose ℳ (T (word j) x) q : M) = x)
    (s : Fin (m + 1) → ℝ) (hs : StrictMono s) (hpos : ∀ j, 0 < s j)
    (htrans : ∀ j, f (word j) (v q) ≠ 0)
    (hsign : ∀ j, SignType.sign (f (word j) (v q)) = ε (word j))
    (hheight : ∀ j, f (word j) (Q + s j • v q) = c (word j))
    (hinc : ∀ j, Q + s j • v q ∈ P (word j))
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + s (Fin.last m) • v q ∈ W j →
      ∀ y ∈ W j, f (word (Fin.last m)) y = c (word (Fin.last m)))
    (hclosedS : ∀ j, IsClosed (S j))
    (hW : ∀ j t, 0 ≤ t → t < s (Fin.last m) →
      (∀ i, t ≠ s i) → Q + t • v q ∉ W j)
    (hS : ∀ j t, 0 ≤ t → t ≤ s (Fin.last m) → Q + t • v q ∉ S j)
    (B : List (Γ × J) → Prop) :
    let Out := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
    let := Fintype.ofFinite Out
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      let In := CutoffDecoratedRay d ℳ T a v f c ε P W S C k
        (Q + (s (Fin.last m) + η) • v q)
      let := Fintype.ofFinite {r : In // r.finalDegree = q}
      (∑ z : Out,
        if z.degreeItinerary.take (m + 1) = List.ofFn (fun j => (q, word j)) ∧
          ((z.degreeItinerary.drop (m + 1)).map Prod.fst).headD 0 = q ∧
          B (z.degreeItinerary.drop (m + 1)) then z.decoration else 0) =
      ∑ r : {r : In // r.finalDegree = q},
        if B r.val.degreeItinerary then r.val.decoration else 0 := by
  classical
  dsimp only
  let t := s (Fin.last m)
  have hcut := eventually_admits_suffix (d := d) (ℳ := ℳ) (T := T) (a := a)
    (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (C := C)
    (k := k) word q t (htrans _) (hheight _)
  have hnear := eventually_extendSegment_notMem Q (v q) s (hpos _).le
    (f (word (Fin.last m))).toLinearMap (c (word (Fin.last m))) (htrans _)
    (hheight _) hclosedW hplane hclosedS hW hS
  filter_upwards [hcut, hnear, self_mem_nhdsWithin] with η hcut hnear hη
  have hη : 0 < η := hη
  let L := t + η
  let Y := Q + L • v q
  let τ (i : Fin (m + 1)) := L - s i
  have hend : Y - L • v q = Q := by simp [Y]
  have hpoint (u : ℝ) : Y - u • v q = Q + (L - u) • v q := by
    dsimp only [Y]
    module
  have hsum := sum_ite_decoration_straightTerminal_eq_sum
    (d := d) (ℳ := ℳ) (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε)
    (P := P) (W := W) (S := S) (C := C) (k := k)
    word q Y hT L (by dsimp only [L]; linarith [hpos (Fin.last m)]) τ
    (fun i j hij => by dsimp only [τ]; linarith [hs hij])
    (fun i => by dsimp only [τ, L]; linarith [hs.monotone (Fin.le_last i)])
    (fun i => by dsimp only [τ]; linarith [hpos i]) htrans hsign
    (fun i => by simpa only [hpoint, τ, sub_sub_cancel] using hheight i)
    (fun i => by simpa only [hpoint, τ, sub_sub_cancel] using hinc i)
    hnear.1 hnear.2 B
  rw [hend] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply propext
  constructor
  · rintro ⟨hp, hq, hB⟩
    obtain ⟨r, hr, hw⟩ := hcut z hp hq
    refine ⟨⟨r, hr⟩, ?_, ?_⟩
    · rw [hw, ← hp, List.take_append_drop]
    · simpa only [hw] using hB
  · rintro ⟨r, hz, hB⟩
    rw [hz]
    simp only [List.length_ofFn, List.take_left', List.drop_left']
    exact ⟨trivial, by simpa only [headD_map_fst_degreeItinerary] using r.property, hB⟩

open Classical in
/-- The complete unchanged-terminal-block sum is the degree-`q` component of
the full incoming cutoff evaluation. All older encounter words are summed,
including the empty word; no domain test remains on outgoing rays. -/
theorem eventually_sum_straightTerminal_eq_component [Finite J] [Finite K]
    (word : Fin (m + 1) → J) (q : Γ)
    (hT : ∀ j x, x ∈ ℳ q → (DirectSum.decompose ℳ (T (word j) x) q : M) = x)
    (s : Fin (m + 1) → ℝ) (hs : StrictMono s) (hpos : ∀ j, 0 < s j)
    (htrans : ∀ j, f (word j) (v q) ≠ 0)
    (hsign : ∀ j, SignType.sign (f (word j) (v q)) = ε (word j))
    (hheight : ∀ j, f (word j) (Q + s j • v q) = c (word j))
    (hinc : ∀ j, Q + s j • v q ∈ P (word j))
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + s (Fin.last m) • v q ∈ W j →
      ∀ y ∈ W j, f (word (Fin.last m)) y = c (word (Fin.last m)))
    (hclosedS : ∀ j, IsClosed (S j))
    (hW : ∀ j t, 0 ≤ t → t < s (Fin.last m) →
      (∀ i, t ≠ s i) → Q + t • v q ∉ W j)
    (hS : ∀ j t, 0 ≤ t → t ≤ s (Fin.last m) → Q + t • v q ∉ S j) :
    let Out := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
      let := Fintype.ofFinite Out
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        (∑ z : Out,
          if z.degreeItinerary.take (m + 1) = List.ofFn (fun j => (q, word j)) ∧
            ((z.degreeItinerary.drop (m + 1)).map Prod.fst).headD 0 = q
          then z.decoration else 0) =
        (DirectSum.decompose ℳ (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
          (Q + (s (Fin.last m) + η) • v q)) q : M) := by
  have h := eventually_sum_straightTerminal_eq_sum (d := d) (ℳ := ℳ) (T := T)
    (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S)
    (C := C) (k := k) word q hT s hs hpos htrans hsign hheight hinc
    hclosedW hplane hclosedS hW hS (fun _ => True)
  filter_upwards [h] with η hη
  simpa only [and_true, ite_true, ← decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree]
    using hη

end Mei.CutoffDecoratedRay
