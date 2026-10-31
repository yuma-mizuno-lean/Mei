/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Localization

/-!
# Incoming decorated rays at their intrinsic cutoff

Cut a decorated ray between two blocks of encounters and put its entire incoming
piece in the all-itinerary inventory at the cutoff given by the degree on the cut
segment. Positive component increments bound every earlier degree by this degree;
no bound on the original ray is needed. The incoming coefficient, all retained
encounters and whole decorations, and source and avoidance conditions persist.
At a degree-changing cut this cutoff is strictly smaller than the final degree,
including changes with unchanged spatial velocity.

The construction uses `DecoratedAdmissibleRay.truncate`,
`CutoffDecoratedRay.lastChangeIndex_spec`, the whole-component
inventory `CutoffDecoratedRay`, and Mathlib's `List.equivSigmaTuple` to package the
retained tuple as a list. This is the incoming piece of the last-change recursion
in Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, §3.3.3 (arXiv:1503.06183v5).
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
  {m n : ℕ}

section Pack

variable {n : ℕ} (word : Fin n → J)
  (r : DecoratedAdmissibleRay ℳ (fun j => T (word j)) 0 a v
    (fun j => f (word j)) (fun j => c (word j))
    (fun j => ε (word j)) (fun j => P (word j)) W S C Q)
  (hmem : ∀ j, r.1.val j ∈ d.cutoff k)
  (hmono : ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)
include hmem hmono in
private theorem exists_inventory : ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
  b.itinerary = List.ofFn word ∧ b.realization.2.ray = r.2.ray ∧
  b.decoration = r.decoration 0 ∧
  b.finalDegree = Fin.snoc (α := fun _ => Γ) r.1.val 0 0 ∧
  b.degreeItinerary = List.ofFn (fun j => (r.1.val j, word j)) ∧
  List.ofFn b.realization.2.parameter = List.ofFn r.2.parameter := by
  obtain ⟨l, hl⟩ := List.equivSigmaTuple.surjective (⟨n, word⟩ : Σ n, Fin n → J)
  cases hl
  refine ⟨⟨l, r, hmem, hmono⟩, ?_, rfl, ?_, ?_, ?_, rfl⟩
  · exact (List.ofFn_get l).symm
  · rw [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero]
  · rw [CutoffDecoratedRay.finalDegree_def]
  · rw [CutoffDecoratedRay.degreeItinerary_eq]

end Pack

namespace DecoratedAdmissibleRay

variable {word : Fin (m + n) → J}
  (r : DecoratedAdmissibleRay ℳ (fun j => T (word j)) 0 a v
    (fun j => f (word j)) (fun j => c (word j))
    (fun j => ε (word j)) (fun j => P (word j)) W S C Q)
  (t : ℝ)
  (hupper : t < r.2.parameter (Fin.natAdd m (0 : Fin (n + 1))))
  (hlower : ∀ j : Fin n, r.2.parameter (Fin.natAdd m j).succ < t)
  (hmem : ∀ j, r.1.val j ∈ d.monoid)
  (hmono : ∀ i j, i ≤ j → r.1.val i - r.1.val j ∈ d.monoid)

include hupper hlower hmem hmono in
/-- The entire incoming piece belongs to the full inventory at its own final
degree cutoff. Its encounter word, complete path, whole decoration, degree
history and every translated encounter parameter are retained. This includes
an empty incoming block. -/
theorem exists_cutoff_truncate :
    let q := Fin.snoc (α := fun _ => Γ) r.1.val 0 (Fin.natAdd m (0 : Fin (n + 1)))
    ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C (d.degree q).toNat (r.2.ray t),
      b.itinerary = List.ofFn (fun j : Fin n => word (Fin.natAdd m j)) ∧
      b.realization.2.ray = r.2.ray.truncate t ∧
      b.decoration = r.decoration (Fin.natAdd m (0 : Fin (n + 1))) ∧
      b.finalDegree = q ∧
      b.degreeItinerary = List.ofFn (fun j : Fin n =>
        (r.1.val (Fin.natAdd m j), word (Fin.natAdd m j))) ∧
      List.ofFn (fun j => b.realization.2.parameter j.succ) =
        List.ofFn (fun j : Fin n => r.2.parameter (Fin.natAdd m j).succ - t) := by
  dsimp only
  let s := r.truncate t hupper hlower
  have hcut : ∀ j : Fin n, s.1.val j ∈ d.cutoff
      (d.degree (Fin.snoc (α := fun _ => Γ) r.1.val 0
        (Fin.natAdd m (0 : Fin (n + 1))))).toNat := by
    intro j
    rw [history_truncate]
    refine d.mem_cutoff.mpr ⟨hmem _, ?_⟩
    let z : Fin n := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
    have hle := d.degree_nonneg (hmono (Fin.natAdd m z) (Fin.natAdd m j)
      (by simp [Fin.le_def, z]))
    have hz : Fin.snoc (α := fun _ => Γ) r.1.val 0
        (Fin.natAdd m (0 : Fin (n + 1))) = r.1.val (Fin.natAdd m z) := by
      have hi : (Fin.natAdd m z).castSucc = Fin.natAdd m (0 : Fin (n + 1)) := by
        ext
        simp [z]
      rw [← hi, Fin.snoc_castSucc]
    rw [map_sub] at hle
    rw [hz]
    exact (sub_nonneg.mp hle).trans (Int.self_le_toNat _)
  have hsub : ∀ i j, i ≤ j → s.1.val i - s.1.val j ∈ d.monoid := by
    intro i j hij
    simp only [s, history_truncate]
    exact hmono _ _ (by simpa only [Fin.le_def, Fin.val_natAdd, Nat.add_le_add_iff_left] using hij)
  obtain ⟨b, hw, hr, ha, hq, hd, hp⟩ :=
    exists_inventory (fun j : Fin n => word (Fin.natAdd m j)) s hcut hsub
  refine ⟨b, hw, hr.trans (r.ray_truncate t hupper hlower), ?_, ?_, ?_, ?_⟩
  · exact ha.trans (r.decoration_truncate t hupper hlower 0)
  · rw [hq, history_truncate]
    exact (congrFun (Fin.snoc_comp_natAdd r.1.val 0) 0).symm
  · simpa only [s, history_truncate] using hd
  · have he : List.ofFn (fun j => b.realization.2.parameter j.succ) =
        List.ofFn (fun j : Fin n => s.2.parameter j.succ) := by
      have he := congrArg List.tail hp
      simpa only [List.ofFn_succ, List.tail_cons] using he
    simpa only [s, parameter_truncate_succ] using he

include hupper hlower hmem hmono in
/-- A cut whose incoming relative degree differs from the final degree produces
an actual ray in a strictly smaller cutoff. All older encounters and degrees,
the source admission and the complete incoming path remain in the inventory.
A change with unchanged spatial velocity still gives strict descent. -/
private theorem exists_cutoff_truncate_lt
    (hne : Fin.snoc (α := fun _ => Γ) r.1.val 0 (Fin.natAdd m (0 : Fin (n + 1))) ≠
      Fin.snoc (α := fun _ => Γ) r.1.val 0 0) :
    ∃ l < (d.degree (Fin.snoc (α := fun _ => Γ) r.1.val 0 0)).toNat,
      ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (r.2.ray t),
        b.itinerary = List.ofFn (fun j : Fin n => word (Fin.natAdd m j)) ∧
        b.realization.2.ray = r.2.ray.truncate t ∧
        b.decoration = r.decoration (Fin.natAdd m (0 : Fin (n + 1))) ∧
        b.finalDegree = Fin.snoc (α := fun _ => Γ) r.1.val 0
          (Fin.natAdd m (0 : Fin (n + 1))) := by
  let b := Fin.snoc (α := fun _ => Γ) r.1.val 0
  let i := Fin.natAdd m (0 : Fin (n + 1))
  have hn : 0 < m + n := by
    by_contra hn
    have hi : i = (0 : Fin (m + n + 1)) := by
      ext
      simp only [i, Fin.val_natAdd, Fin.val_zero, add_zero]
      omega
    exact hne (congrArg b hi)
  let z : Fin (m + n) := ⟨0, hn⟩
  have hz : z.castSucc = (0 : Fin (m + n + 1)) := Fin.ext rfl
  have hstep : b 0 - b i ∈ d.monoid := by
    by_cases hi : i = Fin.last (m + n)
    · simpa only [b, hi, Fin.snoc_last, sub_zero, ← hz, Fin.snoc_castSucc] using hmem z
    · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa only [b, ← hz, ← hj, Fin.snoc_castSucc] using hmono z j (by simp [Fin.le_def, z])
  have hpos := d.degree_pos hstep (sub_ne_zero.mpr hne.symm)
  have hnonneg : 0 ≤ d.degree (b i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [b]
    · simpa only [b, Fin.snoc_castSucc] using d.degree_nonneg (hmem j)
  rw [map_sub] at hpos
  obtain ⟨s, hw, hr, ha, hq, _, _⟩ := r.exists_cutoff_truncate t hupper hlower hmem hmono
  refine ⟨(d.degree (b i)).toNat, ?_, s, hw, hr, ha, hq⟩
  dsimp only [b, i] at hpos hnonneg ⊢
  omega

end DecoratedAdmissibleRay

namespace CutoffDecoratedRay

/-- Cut a cutoff ray before any encounter whose incoming degree differs from
its final degree. The result is a complete incoming inventory ray in a strictly
smaller cutoff, with exactly the older encounters and the original whole
incoming decoration. Later unchanged-degree encounters may be discarded too. -/
theorem exists_cutoff_truncate_lt
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (j : Fin r.itinerary.length) (t : ℝ)
    (hupper : t < r.realization.2.parameter j.succ)
    (hlower : ∀ i : Fin r.itinerary.length, j < i → r.realization.2.parameter i.succ < t)
    (hne : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ ≠ r.finalDegree) :
    ∃ l < (d.degree r.finalDegree).toNat,
      ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (r.realization.2.ray t),
        b.itinerary = r.itinerary.drop (j.val + 1) ∧
        b.realization.2.ray = r.realization.2.ray.truncate t ∧
        b.decoration = r.realization.decoration j.succ ∧
        b.finalDegree = Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ := by
  -- Abstract the length-indexed data before splitting at the selected encounter.
  have cut {N : ℕ} (word : Fin N → J)
      (s : DecoratedAdmissibleRay ℳ (fun i => T (word i)) 0 a v
        (fun i => f (word i)) (fun i => c (word i))
        (fun i => ε (word i)) (fun i => P (word i)) W S C Q)
      (hmem : ∀ i, s.1.val i ∈ d.monoid)
      (hmono : ∀ i l, i ≤ l → s.1.val i - s.1.val l ∈ d.monoid)
      (j : Fin N)
      (hu : t < s.2.parameter j.succ)
      (hl : ∀ i : Fin N, j < i → s.2.parameter i.succ < t)
      (hne : Fin.snoc (α := fun _ => Γ) s.1.val 0 j.succ ≠
        Fin.snoc (α := fun _ => Γ) s.1.val 0 0) :
      ∃ l < (d.degree (Fin.snoc (α := fun _ => Γ) s.1.val 0 0)).toNat,
        ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (s.2.ray t),
          b.itinerary = (List.ofFn word).drop (j.val + 1) ∧
          b.realization.2.ray = s.2.ray.truncate t ∧
          b.decoration = s.decoration j.succ ∧
          b.finalDegree = Fin.snoc (α := fun _ => Γ) s.1.val 0 j.succ := by
    obtain ⟨j, hj⟩ := j
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
    obtain ⟨l, hlt, b, hw, hr, ha, hq⟩ :=
      s.exists_cutoff_truncate_lt (m := j + 1) (n := n) t hu
        (fun i => hl (Fin.natAdd (j + 1) i) (by simp only [Fin.lt_def, Fin.val_natAdd]; omega))
        hmem hmono hne
    refine ⟨l, hlt, b, hw.trans ?_, hr, ha, hq⟩
    rw [List.ofFn_add]
    simp
  simpa only [List.ofFn_get, ← r.finalDegree_def] using
    cut r.itinerary.get r.realization
      (fun i => (d.mem_cutoff.mp (r.degree_mem i)).1)
      r.degree_sub_mem j hupper hlower (by simpa only [← r.finalDegree_def] using hne)

/-- Every ray with nonzero final relative degree has an actual incoming cut
before its canonical last degree change, belonging to a strictly smaller cutoff.
The whole incoming decoration and every older encounter are retained, even when
the selected degree change does not change spatial velocity. -/
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
