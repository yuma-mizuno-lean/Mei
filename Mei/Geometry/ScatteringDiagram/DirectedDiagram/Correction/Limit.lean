/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness
public import Mei.Geometry.ScatteringDiagram.DirectedWall.PureBirth
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Step
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Existence
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Assembly

/-!
# Existence of outgoing completions

A finitely active family of full affine hyperplanes admits a consistent outgoing
completion. Choose successive central corrections coherently, retaining every
previous indexed wall. Each finite stage is a prefix of the next. Their union
has finite activity because walls added after order `k` are invisible at order
`k`; restriction to the order-`k` prefix therefore proves consistency.

The construction uses `exists_chamber_trivialization` and
`LoopProjection.exists_consistent_outgoing_extension` with the identity projection
`LoopProjection.ofFullPure` for the geometric correction, and
`ofBirthFamily`, `ofBirthFamily_consistent_iff` and `Refinement.ofEquiv` for
passage to the union.
Finite correction families are enumerated solely to obtain one countable index
type for the union; repeated walls remain separate occurrences.

The inductive assembly is independent of the geometric correction: a `CorrectionStep`
supplies, for every finite stage consistent at order `k`, a finite outgoing extension
consistent at order `k + 1` whose new walls are invisible at order `k` and have pure birth
logarithms. `exists_outgoingCompletion_of_step` iterates any such step to all orders, with
the logarithms constrained to a chosen set `S`; the full-hyperplane completion takes `S` to
be everything.

This is the compatible induction in Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, proof of Theorem 2.6, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei Mei.Convex

universe u v

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R L ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- The diagram obtained by adjoining the walls of a finite list to `D`, keeping repeated
walls as separate occurrences. -/
def listDiagram (s : List (DirectedWall (d := d) h H)) :
    DirectedDiagram (d := d) h H (ι ⊕ Fin s.length) :=
  D.append (ofFinite (fun j : Fin s.length => s[j]))

@[simp]
theorem listDiagram_wall_inl (s : List (DirectedWall (d := d) h H)) (j : ι) :
    (D.listDiagram s).wall (.inl j) = D.wall j := by simp [listDiagram]

@[simp]
theorem listDiagram_wall_inr (s : List (DirectedWall (d := d) h H)) (j : Fin s.length) :
    (D.listDiagram s).wall (.inr j) = s[j] := by simp [listDiagram]

/-- A one-order correction step for `D` with logarithms in `S`. Every finite list `s` of
outgoing walls with pure birth logarithms in `S` of order at most `k`, adjoined to `D` so
that the result is consistent at order `k`, admits a finite outgoing extension consistent at
order `k + 1`. The extension keeps the walls of `D` and `s`; each added wall is outgoing, has a
pure birth logarithm in `S` of order at most `k + 1`, and is invisible at order `k`. -/
def CorrectionStep (S : Set L) : Prop :=
  ∀ (k : ℕ) (s : List (DirectedWall (d := d) h H)),
    (D.listDiagram s).LevelConsistent k →
    (∀ w ∈ s, w.Outgoing ∧ w.HasPureBirthLog S k) →
    ∃ (κ : Type (max u v)) (_ : Fintype κ)
      (F : DirectedDiagram (d := d) h H ((ι ⊕ Fin s.length) ⊕ κ)),
      (∀ j, F.wall (.inl j) = (D.listDiagram s).wall j) ∧
      F.LevelConsistent (k + 1) ∧
      ∀ a, (F.wall (.inr a)).Outgoing ∧ (F.wall (.inr a)).HasPureBirthLog S (k + 1) ∧
        CompletedGroup.projection k (F.wall (.inr a)).label = 1

/-- Unfolding `CorrectionStep`. -/
theorem correctionStep_def {S : Set L} :
    D.CorrectionStep S ↔
    ∀ (k : ℕ) (s : List (DirectedWall (d := d) h H)),
      (D.listDiagram s).LevelConsistent k →
      (∀ w ∈ s, w.Outgoing ∧ w.HasPureBirthLog S k) →
      ∃ (κ : Type (max u v)) (_ : Fintype κ)
        (F : DirectedDiagram (d := d) h H ((ι ⊕ Fin s.length) ⊕ κ)),
        (∀ j, F.wall (.inl j) = (D.listDiagram s).wall j) ∧
        F.LevelConsistent (k + 1) ∧
        ∀ a, (F.wall (.inr a)).Outgoing ∧ (F.wall (.inr a)).HasPureBirthLog S (k + 1) ∧
          CompletedGroup.projection k (F.wall (.inr a)).label = 1 := Iff.rfl

private def CompletionStage (S : Set L) (k : ℕ) :=
  {s : List (DirectedWall (d := d) h H) //
    (D.listDiagram s).LevelConsistent k ∧ ∀ w ∈ s, w.Outgoing ∧ w.HasPureBirthLog S k}

private theorem exists_next_stage {S : Set L} (step : D.CorrectionStep S)
    {k : ℕ} (s : D.CompletionStage S k) :
    ∃ t : D.CompletionStage S (k + 1), s.val <+: t.val ∧
      ∀ (j : ℕ) (hj : j < t.val.length), s.val.length ≤ j →
        CompletedGroup.projection k t.val[j].label = 1 := by
  classical
  obtain ⟨κ, _, F, hleft, hconsistent, hnew⟩ := step k s.val s.property.1 s.property.2
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
    · simpa [eqv] using hleft (.inl j)
    · simpa [eqv, q, List.getElem_append_left] using hleft (.inr j)
    · simp [eqv, listDiagram, q, r, List.getElem_append_right, e]
  have hq : (D.listDiagram q).LevelConsistent (k + 1) :=
    ((Refinement.ofEquiv eqv hw).levelEquivalent (k + 1)).symm.consistent hconsistent
  refine ⟨⟨q, hq, ?_⟩, ⟨r, rfl⟩, ?_⟩
  · intro w hwq
    rcases List.mem_append.mp hwq with hw | hw
    · exact ⟨(s.property.2 w hw).1, (s.property.2 w hw).2.mono (Nat.le_succ k)⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      exact ⟨(hnew (e j)).1, (hnew (e j)).2.1⟩
  · intro j hj hsj
    have hjr : j - s.val.length < r.length := by simp only [q, List.length_append] at hj; omega
    have hinactive := (hnew (e ⟨j - s.val.length, by simpa [r] using hjr⟩)).2.2
    simpa [q, r, List.getElem_append_right hsj] using hinactive

private theorem exists_completion_stages {S : Set L} (step : D.CorrectionStep S) :
    ∃ stages : ∀ k, D.CompletionStage S k,
      (∀ k m, k ≤ m → (stages k).val <+: (stages m).val) ∧
      ∀ k m, k ≤ m → ∀ (j : ℕ) (hj : j < (stages m).val.length),
        (stages k).val.length ≤ j →
          CompletedGroup.projection k (stages m).val[j].label = 1 := by
  classical
  let base : D.CompletionStage S 0 := ⟨[], by
    refine ⟨(levelConsistent_def _ 0).mpr (fun _ _ _ _ => Subsingleton.elim _ _), ?_⟩
    simp⟩
  let next := fun k (s : D.CompletionStage S k) => (D.exists_next_stage step s).choose
  let stages : ∀ k, D.CompletionStage S k := Nat.rec base next
  have hstep (k : ℕ) : (stages k).val <+: (stages (k + 1)).val ∧
      ∀ (j : ℕ) (hj : j < (stages (k + 1)).val.length), (stages k).val.length ≤ j →
        CompletedGroup.projection k (stages (k + 1)).val[j].label = 1 :=
    (D.exists_next_stage step (stages k)).choose_spec
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

/-- Iterating a one-order correction step with logarithms in `S` gives a consistent outgoing
completion with countably many additional walls, each with a pure birth logarithm in `S`.
No consistency of the initial family is assumed. -/
theorem exists_outgoingCompletion_of_step {S : Set L} (step : D.CorrectionStep S) :
    ∃ (κ : Type) (_ : Countable κ) (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      IsOutgoingCompletion D.wall F ∧ ∀ j, ∃ k, (F.wall (.inr j)).HasPureBirthLog S k := by
  classical
  obtain ⟨stages, hprefix, hinvisible⟩ := D.exists_completion_stages step
  have hlength : Monotone (fun k => (stages k).val.length) :=
    fun k m hkm => (hprefix k m hkm).length_le
  -- An occurrence is a natural-number position that appears in some finite prefix.
  let κ := {j : ℕ // ∃ k, j < (stages k).val.length}
  let W : κ → DirectedWall (d := d) h H := fun j =>
    (stages (Nat.find j.property)).val[j.val]'(Nat.find_spec j.property)
  have hW (k : ℕ) (j : Fin (stages k).val.length) :
      W ⟨j.val, ⟨k, j.isLt⟩⟩ = (stages k).val[j] := by
    have hex : ∃ l, j.val < (stages l).val.length := ⟨k, j.isLt⟩
    let m := Nat.find hex
    have hm : j.val < (stages m).val.length := Nat.find_spec hex
    exact ((hprefix m _ (Nat.le_max_left m k)).getElem hm).trans
      ((hprefix k _ (Nat.le_max_right m k)).getElem j.isLt).symm
  -- Partition corrections by their first stage; the initial diagram is born at zero.
  let birth (j : κ) := Nat.find j.property
  let C (n : ℕ) := {j : κ // birth j = n}
  have hpos (n : ℕ) (j : C n) : j.val.val < (stages n).val.length := by
    exact lt_of_lt_of_le (Nat.find_spec j.val.property)
      (hlength (le_of_eq j.property))
  let (n : ℕ) : Finite (C n) :=
    Finite.of_injective (fun j : C n => (⟨j.val.val, hpos n j⟩ : Fin (stages n).val.length))
      (fun _ _ he => Subtype.ext (Subtype.ext (congrArg Fin.val he)))
  let B (n : ℕ) := (D.restrict {j | 0 = n}).append (ofFinite (fun j : C n => W j.val))
  have hbirth : ∀ n k, k < n → ∀ j, CompletedGroup.projection k ((B n).wall j).label = 1 := by
    intro n k hkn j
    rcases j with j | j
    · have hn : 0 = n := j.property
      omega
    · have hjk : (stages k).val.length ≤ j.val.val := by
        by_contra hj
        have := Nat.find_min' j.val.property (by omega : j.val.val < (stages k).val.length)
        have hn : Nat.find j.val.property = n := j.property
        omega
      simp only [B, append_wall_inr, ofFinite_wall]
      rw [hW n ⟨j.val.val, hpos n j⟩]
      exact hinvisible k n (by omega) j.val.val (hpos n j) hjk
  let A := ofBirthFamily B hbirth
  let e : (Σ n, {j : ι // 0 = n} ⊕ C n) ≃ ι ⊕ κ :=
    (Equiv.sigmaSumDistrib _ _).trans
      (Equiv.sumCongr (Equiv.sigmaFiberEquiv (fun _ : ι => (0 : ℕ)))
        (Equiv.sigmaFiberEquiv birth))
  let F : DirectedDiagram (d := d) h H (ι ⊕ κ) :=
    { wall := A.wall ∘ e.symm
      finite_active := fun k => (A.finite_active k).preimage e.symm.injective.injOn }
  have hF (j) : F.wall j = Sum.elim D.wall W j := by
    cases j <;> simp [F, A, B, e, Equiv.sigmaSumDistrib, Equiv.sigmaFiberEquiv, Sigma.map]
  -- The bounded birth families contain exactly the occurrences in the finite stage.
  have hconsistent : A.Consistent := by
    apply (ofBirthFamily_consistent_iff B hbirth).mpr
    intro k
    let f : ι ⊕ Fin (stages k).val.length → {j : Σ n, {j : ι // 0 = n} ⊕ C n // j.1 ≤ k}
      | .inl j => ⟨⟨0, .inl ⟨j, rfl⟩⟩, Nat.zero_le k⟩
      | .inr j => ⟨⟨birth ⟨j.val, ⟨k, j.isLt⟩⟩, .inr ⟨⟨j.val, ⟨k, j.isLt⟩⟩, rfl⟩⟩,
          Nat.find_min' _ j.isLt⟩
    have hef (j) : e (f j).val = Sum.map id
        (fun j : Fin (stages k).val.length => (⟨j.val, ⟨k, j.isLt⟩⟩ : κ)) j := by
      cases j <;> simp [f, e, Equiv.sigmaSumDistrib, Equiv.sigmaFiberEquiv]
    have hf : Function.Injective f := by
      intro x y he
      exact (Sum.map_injective.mpr ⟨Function.injective_id,
        fun _ _ he => Fin.ext (congrArg Subtype.val he)⟩)
        (by simpa only [hef] using congrArg (fun j => e j.val) he)
    have hs : Function.Surjective f := by
      rintro ⟨⟨n, j | j⟩, hn⟩
      · refine ⟨.inl j.val, Subtype.ext (e.injective ?_)⟩
        simp [f, e, Equiv.sigmaSumDistrib, Equiv.sigmaFiberEquiv]
      · have hjk : j.val.val < (stages k).val.length :=
          lt_of_lt_of_le (hpos n j) (hlength hn)
        refine ⟨.inr ⟨j.val.val, hjk⟩, Subtype.ext (e.injective ?_)⟩
        simp [f, e, Equiv.sigmaSumDistrib, Equiv.sigmaFiberEquiv]
    have hw (j) : (D.listDiagram (stages k).val).wall j =
        (A.restrict {j | j.1 ≤ k}).wall (f j) := by
      cases j with
      | inl j => simp [listDiagram, A, B, f]
      | inr j => simpa only [listDiagram, append_wall_inr, ofFinite_wall,
          restrict_wall, ofBirthFamily_wall, A, B, f] using (hW k j).symm
    exact ((Refinement.ofEquiv (Equiv.ofBijective f ⟨hf, hs⟩) hw).levelEquivalent k).symm.consistent
      (stages k).property.1
  refine ⟨κ, inferInstance, F, ⟨fun j => hF (.inl j), ?_, ?_⟩, ?_⟩
  · intro j
    simpa only [hF, Sum.elim_inr] using
      ((stages (Nat.find j.property)).property.2 (W j)
        (List.getElem_mem (Nat.find_spec j.property))).1
  · exact ((Refinement.ofEquiv (D := F) (E := A) e (by
        intro j
        simp only [F, Function.comp_apply, Equiv.symm_apply_apply])).equivalent.consistent_iff).mpr
      hconsistent
  · intro j
    exact ⟨Nat.find j.property, by
      simpa only [hF, Sum.elim_inr] using
        ((stages (Nat.find j.property)).property.2 (W j)
          (List.getElem_mem (Nat.find_spec j.property))).2⟩

variable [Module.Free ℤ Γ]

/-- Over full affine hyperplanes, the one-order correction at any consistent finite stage
admits a finite outgoing extension, with no restriction on the logarithms. -/
private theorem correctionStep_univ
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) :
    D.CorrectionStep (Set.univ : Set L) := by
  classical
  intro k s hk hs
  let E := D.listDiagram s
  obtain ⟨σ, hσ, cross, b, _, t, ht, τ, hτ, _⟩ :=
    E.exists_chamber_trivialization hk (fun _ => 1) (fun _ => zero_lt_one)
  obtain ⟨κ, _, F, hleft, hconsistent, _, hnew⟩ :=
    (LoopProjection.ofFullPure E (range (Sum.inl : ι → ι ⊕ Fin s.length))
      (by rintro (j | j) hj
          · simpa only [E, listDiagram_wall_inl] using hfull j
          · simp at hj)
      (by rintro (j | j) hj
          · exact (hj ⟨j, rfl⟩).elim
          · obtain ⟨n, hn, hd, a, ha, _, he, _⟩ := DirectedWall.hasPureBirthLog_def.mp
              (hs s[j] (List.getElem_mem j.isLt)).2
            exact ⟨n, by omega, a, ha, by simpa only [E, listDiagram_wall_inr] using he⟩)
      ).exists_consistent_outgoing_extension
      σ hσ cross hk b t ht τ hτ
  refine ⟨κ, inferInstance, F, hleft, hconsistent, fun a => ?_⟩
  obtain ⟨hout, ⟨n, hn, hd, z, hz, hlabel⟩, hborn, _⟩ := hnew a
  refine ⟨hout, DirectedWall.hasPureBirthLog_def.mpr
    ⟨n, hn, by omega, z, hz, trivial, hlabel, fun l => ?_⟩, ?_⟩
  · simpa only [mem_active] using (hborn l).trans (by omega : k + 1 ≤ l ↔ d.degree n ≤ l)
  · simpa only [mem_active, Nat.not_succ_le_self, iff_false, not_not] using hborn k

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
  obtain ⟨κ, hκ, F, hF, hbirth⟩ :=
    D.exists_outgoingCompletion_of_step (D.correctionStep_univ hfull)
  refine ⟨κ, hκ, F, hF, fun j => ?_⟩
  obtain ⟨k, hk⟩ := hbirth j
  obtain ⟨n, hn, _, a, ha, _, hlabel, hproj⟩ := DirectedWall.hasPureBirthLog_def.mp hk
  exact ⟨n, hn, a, ha, hlabel, fun l => by simpa only [mem_active] using hproj l⟩

end Mei.DirectedDiagram
