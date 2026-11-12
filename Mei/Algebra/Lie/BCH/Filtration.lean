/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutators in the degree filtration of completed BCH groups

The degree filtration of a completed positively graded BCH group satisfies
`[Fᵃ, Fᵇ] ≤ Fᵃ⁺ᵇ`. Thus an element born in degree `a` commutes with one born
in degree `b` at every order below `a + b`. In particular, the successive
filtration quotients are central, as needed for constructions by degree induction.

In finite Lie quotients, `commute_exp_mk_of_mem_degreeIdeal` says that elements of
`truncationIdeal ℒ a` and `truncationIdeal ℒ b` have commuting exponentials modulo
`truncationIdeal ℒ (a + b + 1)`. This specializes the vanishing-bracket criterion
`BCHGroup.commute_exp_of_lie_eq_zero` using the degree bound
`PositiveDegrees.lie_truncationIdeal_le`. Its completed counterpart,
`commutator_degreeFiltration_le`, bounds commutators at all filtration orders.
The original Lie algebra need not be nilpotent, and no freeness assumption is used.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open scoped commutatorElement

namespace TauCeti.PositiveDegrees

open Mei

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Exponentials of terms above cutoffs `a` and `b` commute at order `a + b + 1`. -/
theorem commute_exp_mk_of_mem_degreeIdeal {a b : ℕ} {x y : L}
    (hx : x ∈ d.truncationIdeal ℒ a) (hy : y ∈ d.truncationIdeal ℒ b) :
    Commute (BCHGroup.exp ((d.truncationIdeal ℒ (a + b + 1)).mkQ x))
      (BCHGroup.exp ((d.truncationIdeal ℒ (a + b + 1)).mkQ y)) := by
  apply BCHGroup.commute_exp_of_lie_eq_zero
  rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero]
  exact d.lie_truncationIdeal_le ℒ a b (LieSubmodule.lie_mem_lie hx hy)

/-- A representative of the logarithm at a higher order lies above cutoff `a`
exactly when the completed element vanishes at order `a`. -/
theorem mem_degreeIdeal_iff_of_mkQ_eq_log_projection {a k : ℕ} (hak : a ≤ k)
    (g : d.completedBCHGroup ℒ) {x : L}
    (hx : (d.truncationIdeal ℒ k).mkQ x =
      BCHGroup.log (L := d.lieTruncation ℒ k) (TauCeti.CompletedGroup.projection k g)) :
    x ∈ d.truncationIdeal ℒ a ↔
      g ∈ TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) := by
  have hcompat :
      (d.lieTruncationMap ℒ hak).bchGroupMap (TauCeti.CompletedGroup.projection k g) =
        TauCeti.CompletedGroup.projection a g :=
    TauCeti.CompletedGroup.map_projection a k hak g
  have hlog := congrArg (BCHGroup.log (L := d.lieTruncation ℒ a)) hcompat
  rw [(d.lieTruncationMap ℒ hak).log_bchGroupMap
    (TauCeti.CompletedGroup.projection k g), ← hx, LieIdeal.mkQ_apply, lieTruncationMap_mk] at hlog
  rw [TauCeti.CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker]
  constructor
  · intro hx'
    exact BCHGroup.log_injective (L := d.lieTruncation ℒ a)
      (hlog.symm.trans (((d.truncationIdeal ℒ a).mkQ_eq_zero.mpr hx').trans
        (BCHGroup.log_one (L := d.lieTruncation ℒ a)).symm))
  · intro hg
    exact (d.truncationIdeal ℒ a).mkQ_eq_zero.mp
      (hlog.trans ((congrArg (BCHGroup.log (L := d.lieTruncation ℒ a)) hg).trans
        (BCHGroup.log_one (L := d.lieTruncation ℒ a))))

/-- Every completed BCH element has strictly positive degree. -/
@[simp↓]
theorem degreeFiltration_one :
    TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) 1 = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := (d.truncationIdeal ℒ 0).surjective_mkQ
    (BCHGroup.log (L := d.lieTruncation ℒ 0) (TauCeti.CompletedGroup.projection 0 g))
  exact (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ le_rfl g hx).mp
    (by simp)

/-- Positive filtration orders add under group commutators. -/
private theorem commutator_mem_degreeFiltration_succ {a b : ℕ}
    {g h : d.completedBCHGroup ℒ}
    (hg : g ∈ TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    (hh : h ∈ TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (b + 1)) :
    ⁅g, h⁆ ∈ TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + b + 2) := by
  obtain ⟨x, hx⟩ := (d.truncationIdeal ℒ (a + b + 1)).surjective_mkQ
    (BCHGroup.log (L := d.lieTruncation ℒ (a + b + 1))
      (TauCeti.CompletedGroup.projection (a + b + 1) g))
  obtain ⟨y, hy⟩ := (d.truncationIdeal ℒ (a + b + 1)).surjective_mkQ
    (BCHGroup.log (L := d.lieTruncation ℒ (a + b + 1))
      (TauCeti.CompletedGroup.projection (a + b + 1) h))
  have hxa := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ
    (by omega : a ≤ a + b + 1) g hx).mpr hg
  have hyb := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ
    (by omega : b ≤ a + b + 1) h hy).mpr hh
  have hc := d.commute_exp_mk_of_mem_degreeIdeal ℒ hxa hyb
  rw [hx, hy,
    BCHGroup.exp_log (L := d.lieTruncation ℒ (a + b + 1))
      (TauCeti.CompletedGroup.projection (a + b + 1) g),
    BCHGroup.exp_log (L := d.lieTruncation ℒ (a + b + 1))
      (TauCeti.CompletedGroup.projection (a + b + 1) h)] at hc
  have hab : a + b + 2 = (a + b + 1) + 1 := by omega
  rw [hab, TauCeti.CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker,
    map_commutatorElement]
  exact hc.commutator_eq

/-- The commutator of two degree-filtration subgroups lies in their combined
filtration order, including when either input order is zero. -/
theorem commutator_degreeFiltration_le (a b : ℕ) :
    ⁅TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) a,
      TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) b⁆ ≤
        TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + b) := by
  cases a with
  | zero =>
    simpa using Subgroup.commutator_le_right
      (TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) 0)
      (TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) b)
  | succ a =>
    cases b with
    | zero =>
      simpa using Subgroup.commutator_le_left
        (TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
        (TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) 0)
    | succ b =>
      apply Subgroup.commutator_le.mpr
      intro g hg h hh
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using d.commutator_mem_degreeFiltration_succ ℒ hg hh

/-- Commuting with an arbitrary completed element raises the filtration order.
Consequently each successive filtration quotient is central in the corresponding
quotient of the completed group. -/
theorem commutator_top_degreeFiltration_le (k : ℕ) :
    ⁅(⊤ : Subgroup (d.completedBCHGroup ℒ)),
      TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) k⁆ ≤
        TauCeti.CompletedGroup.degreeFiltration (d.groupTower ℒ) (k + 1) := by
  simpa only [degreeFiltration_one, Nat.add_comm 1 k] using
    d.commutator_degreeFiltration_le ℒ 1 k

end TauCeti.PositiveDegrees
