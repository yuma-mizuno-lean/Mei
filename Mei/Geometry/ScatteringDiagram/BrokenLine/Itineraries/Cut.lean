/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

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
`CutoffDecoratedRay.exists_of_word` to package the retained tuple as a list,
and `CutoffDecoratedRay.degree_lt_finalDegree_of_ne` for strict descent. This is
the incoming piece of the last-change recursion
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
degree cutoff. Its encounter word, complete incoming path (the ray truncated
at `t`), whole decoration, degree history and every translated encounter parameter
are retained. This includes an empty incoming block. -/
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
    CutoffDecoratedRay.exists_of_word (fun j : Fin n => word (Fin.natAdd m j)) s hcut hsub
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
/-- A strict bound on the incoming degree gives an inventory ray at a strictly
smaller cutoff, retaining the complete incoming path and older encounters. -/
private theorem exists_cutoff_truncate_lt
    (hlt : d.degree (Fin.snoc (α := fun _ => Γ) r.1.val 0
        (Fin.natAdd m (0 : Fin (n + 1)))) <
      d.degree (Fin.snoc (α := fun _ => Γ) r.1.val 0 0)) :
    ∃ l < (d.degree (Fin.snoc (α := fun _ => Γ) r.1.val 0 0)).toNat,
      ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (r.2.ray t),
        b.itinerary = List.ofFn (fun j : Fin n => word (Fin.natAdd m j)) ∧
        b.realization.2.ray = r.2.ray.truncate t ∧
        b.decoration = r.decoration (Fin.natAdd m (0 : Fin (n + 1))) ∧
        b.finalDegree = Fin.snoc (α := fun _ => Γ) r.1.val 0
          (Fin.natAdd m (0 : Fin (n + 1))) ∧
        b.degreeItinerary = List.ofFn (fun j : Fin n =>
          (r.1.val (Fin.natAdd m j), word (Fin.natAdd m j))) := by
  let b := Fin.snoc (α := fun _ => Γ) r.1.val 0
  let i := Fin.natAdd m (0 : Fin (n + 1))
  have hnonneg : 0 ≤ d.degree (b i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [b]
    · simpa only [b, Fin.snoc_castSucc] using d.degree_nonneg (hmem j)
  obtain ⟨s, hw, hr, ha, hq, hd, _⟩ := r.exists_cutoff_truncate t hupper hlower hmem hmono
  refine ⟨(d.degree (b i)).toNat, ?_, s, hw, hr, ha, hq, hd⟩
  dsimp only [b, i] at hnonneg ⊢
  omega

end DecoratedAdmissibleRay

namespace CutoffDecoratedRay

/-- Cut a cutoff ray before any encounter whose incoming degree differs from
its final degree. The result is a complete incoming inventory ray in a strictly
smaller cutoff, with exactly the older encounters and the original whole
incoming decoration. The selected encounter and all later encounters are
discarded. -/
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
        b.finalDegree = Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ ∧
        b.degreeItinerary = r.degreeItinerary.drop (j.val + 1) := by
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
      (hlt : d.degree (Fin.snoc (α := fun _ => Γ) s.1.val 0 j.succ) <
        d.degree (Fin.snoc (α := fun _ => Γ) s.1.val 0 0)) :
      ∃ l < (d.degree (Fin.snoc (α := fun _ => Γ) s.1.val 0 0)).toNat,
        ∃ b : CutoffDecoratedRay d ℳ T a v f c ε P W S C l (s.2.ray t),
          b.itinerary = (List.ofFn word).drop (j.val + 1) ∧
          b.realization.2.ray = s.2.ray.truncate t ∧
          b.decoration = s.decoration j.succ ∧
          b.finalDegree = Fin.snoc (α := fun _ => Γ) s.1.val 0 j.succ ∧
          b.degreeItinerary =
            (List.ofFn (fun i => (s.1.val i, word i))).drop (j.val + 1) := by
    obtain ⟨j, hj⟩ := j
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
    obtain ⟨l, hlt, b, hw, hr, ha, hq, hd⟩ :=
      s.exists_cutoff_truncate_lt (m := j + 1) (n := n) t hu
        (fun i => hl (Fin.natAdd (j + 1) i) (by simp only [Fin.lt_def, Fin.val_natAdd]; omega))
        hmem hmono hlt
    refine ⟨l, hlt, b, hw.trans ?_, hr, ha, hq, hd.trans ?_⟩
    · rw [List.ofFn_add]
      simp
    · rw [List.ofFn_add]
      simp
  simpa only [List.ofFn_get, ← r.finalDegree_def, ← r.degreeItinerary_eq] using
    cut r.itinerary.get r.realization
      (fun i => (d.mem_cutoff.mp (r.degree_mem i)).1)
      r.degree_sub_mem j hupper hlower
      (by simpa only [← r.finalDegree_def] using r.degree_lt_finalDegree_of_ne j hne)

end CutoffDecoratedRay

end Mei
