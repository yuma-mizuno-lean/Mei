/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Step
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Existence
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append

/-!
# Existence of outgoing completions

A finitely active family of full affine hyperplanes admits a consistent outgoing
completion. Choose successive central corrections coherently, retaining every
previous indexed wall. Each finite stage is a prefix of the next. Their union
has finite activity because walls added after order `k` are invisible at order
`k`; restriction to the order-`k` prefix therefore proves consistency.

The construction uses `exists_chamber_trivialization` and
`exists_consistent_outgoing_extension` for the geometric correction, and
`levelEquivalent_restrict` and `Refinement.ofEquiv` for passage to the union.
Finite correction families are enumerated solely to obtain one countable index
type for the union; repeated walls remain separate occurrences.

This is the compatible induction in Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, proof of Theorem 2.6, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

private def listDiagram (s : List (DirectedWall (d := d) h H)) :=
  D.append (ofFinite (fun j : Fin s.length => s[j]))

private def CompletionStage (k : ℕ) :=
  {s : List (DirectedWall (d := d) h H) //
    (D.listDiagram s).LevelConsistent k ∧
    ∀ w ∈ s, w.Outgoing ∧ ∃ n ∈ w.ray.rayDegrees,
      d.degree n ≤ k ∧ ∃ a ∈ ℒ n, w.label = d.expToCompletion ℒ a ∧
        ∀ l : ℕ, CompletedGroup.projection l w.label ≠ 1 ↔ d.degree n ≤ l}

private theorem exists_next_stage
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a})
    {k : ℕ} (s : D.CompletionStage k) :
    ∃ t : D.CompletionStage (k + 1), s.val <+: t.val ∧
      ∀ (j : ℕ) (hj : j < t.val.length), s.val.length ≤ j →
        CompletedGroup.projection k t.val[j].label = 1 := by
  classical
  let E := D.listDiagram s.val
  obtain ⟨σ, hσ, cross, b, _, t, ht, τ, hτ, _⟩ :=
    E.exists_chamber_trivialization s.property.1 (fun _ => 1) (fun _ => zero_lt_one)
  obtain ⟨κ, _, F, hleft, hconsistent, _, hnew⟩ :=
    exists_consistent_outgoing_extension σ hσ cross s.property.1 b t ht τ hτ
      (range (Sum.inl : ι → ι ⊕ Fin s.val.length))
      (by rintro (j | j) hj
          · simpa only [E, listDiagram, append_wall_inl] using hfull j
          · simp at hj)
      (by rintro (j | j) hj
          · exact (hj ⟨j, rfl⟩).elim
          · obtain ⟨_, n, _, hn, a, ha, he⟩ :=
              s.property.2 s.val[j] (List.getElem_mem j.isLt)
            refine ⟨n, by omega, a, ha, ?_⟩
            simpa only [E, listDiagram, append_wall_inr, ofFinite_wall] using he.1)
  -- Enumerate only the new corrections and append them, preserving every old position.
  let e := (Fintype.equivFin κ).symm
  let r := List.ofFn (fun j => F.wall (.inr (e j)))
  let q := s.val ++ r
  let eqv : (ι ⊕ Fin s.val.length) ⊕ κ ≃ ι ⊕ Fin q.length :=
    (Equiv.sumAssoc _ _ _).trans
      (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _)
        (Fintype.equivFin κ)).trans (finSumFinEquiv.trans (finCongr (by simp [q, r])))))
  have hw (j) : F.wall j = (D.listDiagram q).wall (eqv j) := by
    rcases j with (j | j) | j
    · simpa [eqv, E, listDiagram] using hleft (.inl j)
    · simpa [eqv, E, listDiagram, q, List.getElem_append_left] using hleft (.inr j)
    · simp [eqv, listDiagram, q, r, List.getElem_append_right, e]
  have hq : (D.listDiagram q).LevelConsistent (k + 1) :=
    ((Refinement.ofEquiv eqv hw).levelEquivalent (k + 1)).symm.consistent hconsistent
  refine ⟨⟨q, hq, ?_⟩, ⟨r, rfl⟩, ?_⟩
  · intro w hwq
    rcases List.mem_append.mp hwq with hw | hw
    · obtain ⟨ho, n, hn, hd, a, ha, he⟩ := s.property.2 w hw
      exact ⟨ho, n, hn, hd.trans (by omega), a, ha, he⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      obtain ⟨ho, n, hn, hd, a, ha, he⟩ := (hnew (e j)).1, (hnew (e j)).2.1
      refine ⟨ho, n, hn, by omega, a, ha, he, ?_⟩
      intro l
      have hb := (hnew (e j)).2.2 l
      simp only [mem_active] at hb
      exact hb.trans (by omega)
  · intro j hj hsj
    have hjr : j - s.val.length < r.length := by simp only [q, List.length_append] at hj; omega
    have hborn := (hnew (e ⟨j - s.val.length, by simpa [r] using hjr⟩)).2.2 k
    have hinactive : CompletedGroup.projection k
        (F.wall (.inr (e ⟨j - s.val.length, by simpa [r] using hjr⟩))).label = 1 := by
      simpa only [mem_active, Nat.not_succ_le_self, iff_false, not_not] using hborn
    simpa [q, r, List.getElem_append_right hsj] using hinactive

private theorem exists_completion_stages
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) :
    ∃ stages : ∀ k, D.CompletionStage k,
      (∀ k m, k ≤ m → (stages k).val <+: (stages m).val) ∧
      ∀ k m, k ≤ m → ∀ (j : ℕ) (hj : j < (stages m).val.length),
        (stages k).val.length ≤ j →
          CompletedGroup.projection k (stages m).val[j].label = 1 := by
  classical
  let base : D.CompletionStage 0 := ⟨[], by
    refine ⟨(levelConsistent_def _ 0).mpr (fun _ _ _ _ => Subsingleton.elim _ _), ?_⟩
    simp⟩
  let next := fun k (s : D.CompletionStage k) => (D.exists_next_stage hfull s).choose
  let stages : ∀ k, D.CompletionStage k := Nat.rec base next
  have hstep (k : ℕ) : (stages k).val <+: (stages (k + 1)).val ∧
      ∀ (j : ℕ) (hj : j < (stages (k + 1)).val.length), (stages k).val.length ≤ j →
        CompletedGroup.projection k (stages (k + 1)).val[j].label = 1 :=
    (D.exists_next_stage hfull (stages k)).choose_spec
  have hprefix {k m : ℕ} (hkm : k ≤ m) : (stages k).val <+: (stages m).val := by
    induction m, hkm using Nat.le_induction with
    | base => exact ⟨[], by simp⟩
    | succ m _ ih => exact ih.trans (hstep m).1
  refine ⟨stages, fun _ _ hkm => hprefix hkm, ?_⟩
  -- New positions remain invisible at every earlier cutoff, even after further extensions.
  intro k m hkm
  induction m, hkm using Nat.le_induction with
  | base => intros; omega
  | succ m hkm ih =>
    intro j hj hkj
    by_cases hjm : j < (stages m).val.length
    · rw [← (hstep m).1.getElem hjm]
      exact ih j hjm hkj
    · have he := CompletedGroup.map_projection k m hkm (stages (m + 1)).val[j].label
      rw [(hstep m).2 j hj (by omega), map_one] at he
      exact he.symm

/-- A finitely active family of full affine hyperplanes has a consistent outgoing
completion with countably many additional walls. Each added label has a homogeneous
logarithm in an actual degree of its supported ray and is active exactly from that
degree onward. No consistency of the initial family is assumed. -/
theorem exists_outgoingCompletion
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) :
    ∃ (κ : Type) (_ : Countable κ) (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      IsOutgoingCompletion D.wall F ∧
      ∀ j, ∃ n ∈ (F.wall (.inr j)).ray.rayDegrees,
        ∃ a ∈ ℒ n, (F.wall (.inr j)).label = d.expToCompletion ℒ a ∧
          ∀ k : ℕ, Sum.inr j ∈ F.active k ↔ d.degree n ≤ k := by
  classical
  obtain ⟨stages, hprefix, hinvisible⟩ := D.exists_completion_stages hfull
  have hlength : Monotone (fun k => (stages k).val.length) :=
    fun k m hkm => (hprefix k m hkm).length_le
  -- An occurrence is a natural-number position that appears in some finite prefix.
  let κ := {j : ℕ // ∃ k, j < (stages k).val.length}
  let W : κ → DirectedWall (d := d) h H := fun j =>
    (stages (Nat.find j.property)).val[j.val]'(Nat.find_spec j.property)
  have hW (k : ℕ) (j : Fin (stages k).val.length) :
      W ⟨j.val, ⟨k, j.isLt⟩⟩ = (stages k).val[j] := by
    let m := Nat.find (show ∃ l, j.val < (stages l).val.length from ⟨k, j.isLt⟩)
    have hm : j.val < (stages m).val.length :=
      Nat.find_spec (show ∃ l, j.val < (stages l).val.length from ⟨k, j.isLt⟩)
    exact ((hprefix m _ (Nat.le_max_left m k)).getElem hm).trans
      ((hprefix k _ (Nat.le_max_right m k)).getElem j.isLt).symm
  have hbound (k : ℕ) (j : κ) (hj : CompletedGroup.projection k (W j).label ≠ 1) :
      j.val < (stages k).val.length := by
    by_contra hjk
    have hm := Nat.find_spec j.property
    have hkm : k ≤ Nat.find j.property := by
      by_contra hmk
      have := hlength (Nat.le_of_lt (Nat.lt_of_not_ge hmk))
      exact hjk (lt_of_lt_of_le hm this)
    exact hj (hinvisible k _ hkm j.val hm (by omega))
  let E : DirectedDiagram (d := d) h H κ :=
    { wall := W
      finite_active := fun k => by
        apply ((finite_Iio (stages k).val.length).preimage
          (Subtype.val_injective.injOn : Set.InjOn (Subtype.val : κ → ℕ) _)).subset
        intro j hj
        exact hbound k j hj }
  let F := D.append E
  -- At each cutoff the union restricts, up to reindexing, to its consistent finite stage.
  have hfinite (k : ℕ) : F.LevelEquivalent (D.listDiagram (stages k).val) k := by
    let f : ι ⊕ Fin (stages k).val.length → ι ⊕ κ :=
      Sum.map id (fun j => ⟨j.val, ⟨k, j.isLt⟩⟩)
    have hf : Function.Injective f := Sum.map_injective.mpr
      ⟨Function.injective_id, fun _ _ he => Fin.ext (congrArg Subtype.val he)⟩
    have hactive : F.active k ⊆ range f := by
      rintro (j | j) hj
      · exact ⟨.inl j, rfl⟩
      · have hjk := hbound k j (by simpa only [mem_active, F, append_wall_inr] using hj)
        exact ⟨.inr ⟨j.val, hjk⟩, congrArg Sum.inr (Subtype.ext rfl)⟩
    have hreindex : (F.restrict (range f)).LevelEquivalent
        (D.listDiagram (stages k).val) k :=
      (Refinement.ofEquiv (Equiv.ofInjective f hf) (by
        rintro (j | j)
        · simp [listDiagram, F, f, Equiv.ofInjective_apply]
        · simp [listDiagram, F, f, E, hW, Equiv.ofInjective_apply])).levelEquivalent k
    exact (F.levelEquivalent_restrict hactive).trans hreindex
  refine ⟨κ, inferInstance, F, ⟨fun _ => append_wall_inl _ _ _, ?_, ?_⟩, ?_⟩
  · intro j
    simpa only [F, append_wall_inr, E] using
      ((stages (Nat.find j.property)).property.2 (W j)
        (List.getElem_mem (Nat.find_spec j.property))).1
  · exact (F.consistent_iff).mpr fun k =>
      (hfinite k).symm.consistent (stages k).property.1
  · intro j
    obtain ⟨_, n, hn, _, a, ha, he, hb⟩ :=
      (stages (Nat.find j.property)).property.2 (W j)
        (List.getElem_mem (Nat.find_spec j.property))
    simpa only [F, append_wall_inr, E, mem_active] using ⟨n, hn, a, ha, he, hb⟩

end Mei.DirectedDiagram
