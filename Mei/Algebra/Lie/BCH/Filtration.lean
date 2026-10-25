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

The argument uses `PositiveDegrees.lie_degreeIdeal_le` and
`BCHGroup.commute_exp_of_lie_eq_zero` in finite Lie quotients. Compatibility of
`CompletedGroup.projection` detects the filtration membership of representatives;
Mathlib's `Subgroup.commutator_le` then gives the subgroup estimate. The original
Lie algebra need not be nilpotent, and no freeness assumption is used.
-/

public section

open scoped commutatorElement

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Exponentials of terms above cutoffs `a` and `b` commute at order `a + b + 1`. -/
theorem commute_exp_mk_of_mem_degreeIdeal {a b : ℕ} {x y : L}
    (hx : x ∈ d.degreeIdeal ℒ a) (hy : y ∈ d.degreeIdeal ℒ b) :
    Commute (BCHGroup.exp ((d.degreeIdeal ℒ (a + b + 1)).mkQ x))
      (BCHGroup.exp ((d.degreeIdeal ℒ (a + b + 1)).mkQ y)) := by
  apply BCHGroup.commute_exp_of_lie_eq_zero
  rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero]
  exact d.lie_degreeIdeal_le ℒ a b (LieSubmodule.lie_mem_lie hx hy)

/-- A representative of the logarithm at a higher order lies above cutoff `a`
exactly when the completed element vanishes at order `a`. -/
private theorem mem_degreeIdeal_iff_of_mkQ_eq_log_projection {a k : ℕ} (hak : a ≤ k)
    (g : d.completedBCHGroup ℒ) {x : L}
    (hx : (d.degreeIdeal ℒ k).mkQ x =
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g)) :
    x ∈ d.degreeIdeal ℒ a ↔
      g ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) := by
  have hcompat :
      (d.truncationMap ℒ hak).bchGroupMap (CompletedGroup.projection k g) =
        CompletedGroup.projection a g :=
    CompletedGroup.map_projection a k hak g
  have hlog := congrArg (BCHGroup.log (L := d.truncatedLie ℒ a)) hcompat
  rw [(d.truncationMap ℒ hak).log_bchGroupMap
    (CompletedGroup.projection k g), ← hx, LieIdeal.mkQ_apply, truncationMap_mk] at hlog
  rw [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker]
  constructor
  · intro hx'
    exact BCHGroup.log_injective (L := d.truncatedLie ℒ a)
      (hlog.symm.trans (((d.degreeIdeal ℒ a).mkQ_eq_zero.mpr hx').trans
        (BCHGroup.log_one (L := d.truncatedLie ℒ a)).symm))
  · intro hg
    exact (d.degreeIdeal ℒ a).mkQ_eq_zero.mp
      (hlog.trans ((congrArg (BCHGroup.log (L := d.truncatedLie ℒ a)) hg).trans
        (BCHGroup.log_one (L := d.truncatedLie ℒ a))))

/-- Every completed BCH element has strictly positive degree. -/
@[simp↓]
theorem degreeFiltration_one :
    CompletedGroup.degreeFiltration (d.groupTower ℒ) 1 = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ 0).surjective_mkQ
    (BCHGroup.log (L := d.truncatedLie ℒ 0) (CompletedGroup.projection 0 g))
  exact (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ le_rfl g hx).mp
    (by simp)

/-- Positive filtration orders add under group commutators. -/
private theorem commutator_mem_degreeFiltration_succ {a b : ℕ}
    {g h : d.completedBCHGroup ℒ}
    (hg : g ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    (hh : h ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (b + 1)) :
    ⁅g, h⁆ ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + b + 2) := by
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ (a + b + 1)).surjective_mkQ
    (BCHGroup.log (L := d.truncatedLie ℒ (a + b + 1))
      (CompletedGroup.projection (a + b + 1) g))
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ (a + b + 1)).surjective_mkQ
    (BCHGroup.log (L := d.truncatedLie ℒ (a + b + 1))
      (CompletedGroup.projection (a + b + 1) h))
  have hxa := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ
    (by omega : a ≤ a + b + 1) g hx).mpr hg
  have hyb := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ
    (by omega : b ≤ a + b + 1) h hy).mpr hh
  have hc := d.commute_exp_mk_of_mem_degreeIdeal ℒ hxa hyb
  rw [hx, hy,
    BCHGroup.exp_log (L := d.truncatedLie ℒ (a + b + 1))
      (CompletedGroup.projection (a + b + 1) g),
    BCHGroup.exp_log (L := d.truncatedLie ℒ (a + b + 1))
      (CompletedGroup.projection (a + b + 1) h)] at hc
  have hab : a + b + 2 = (a + b + 1) + 1 := by omega
  rw [hab, CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker,
    map_commutatorElement]
  exact hc.commutator_eq

/-- The commutator of two degree-filtration subgroups lies in their combined
filtration order, including when either input order is zero. -/
theorem commutator_degreeFiltration_le (a b : ℕ) :
    ⁅CompletedGroup.degreeFiltration (d.groupTower ℒ) a,
      CompletedGroup.degreeFiltration (d.groupTower ℒ) b⁆ ≤
        CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + b) := by
  cases a with
  | zero =>
    simpa using Subgroup.commutator_le_right
      (CompletedGroup.degreeFiltration (d.groupTower ℒ) 0)
      (CompletedGroup.degreeFiltration (d.groupTower ℒ) b)
  | succ a =>
    cases b with
    | zero =>
      simpa using Subgroup.commutator_le_left
        (CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
        (CompletedGroup.degreeFiltration (d.groupTower ℒ) 0)
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
      CompletedGroup.degreeFiltration (d.groupTower ℒ) k⁆ ≤
        CompletedGroup.degreeFiltration (d.groupTower ℒ) (k + 1) := by
  simpa only [degreeFiltration_one, Nat.add_comm 1 k] using
    d.commutator_degreeFiltration_le ℒ 1 k

end Mei.PositiveDegrees
