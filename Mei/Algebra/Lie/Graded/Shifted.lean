/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted
public import Mei.Algebra.Lie.Filtered.Action

/-!
# Positive Lie actions on shifted coefficient modules

A positively graded Lie algebra preserves the module supported in any translate
`p + P` of its positive monoid. On this module, the action raises relative degree:
a Lie element above cutoff `a` sends coefficients of order `b` to order
`a + b + 1`. Thus the existing filtered Lie representations and their
characteristic-zero exponential actions apply to shifted coefficients.

The relative filtration is `PositiveDegrees.shiftedFiltration`; its presentation
on a `LieSubmodule` retains Mathlib's restricted Lie action. The construction uses
`SetLike.GradedBracket.bracket_mem` and the homogeneous decomposition, with no
positivity requirement on the ambient coefficient grading.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open Mei

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [hℒ : DirectSum.Decomposition ℒ] [hpos : IsPositiveGrading d ℒ]
  [hbr : SetLike.GradedBracket ℒ ℳ] (p : Γ)

include hℒ hpos hbr

/-- Positive Lie degrees preserve coefficients supported on `p + P`. -/
theorem lie_mem_shiftedSubmodule (x : L) {y : M} (hy : y ∈ shiftedSubmodule ℳ d.monoid p) :
    ⁅x, y⁆ ∈ shiftedSubmodule ℳ d.monoid p := by
  rw [shiftedSubmodule_def] at hy
  induction x using DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · refine Submodule.iSup_induction (fun m : d.monoid => ℳ (p + m))
        (motive := fun y => ⁅(x : L), y⁆ ∈ shiftedSubmodule ℳ d.monoid p) hy ?_ ?_ ?_
      · intro m y hy
        apply le_shiftedSubmodule ℳ d.monoid p (d.monoid.add_mem hn m.property)
        simpa only [vadd_eq_add, add_comm, add_left_comm, add_assoc] using
          SetLike.GradedBracket.bracket_mem x.property hy
      · simp
      · intro y z hy hz
        simpa [lie_add] using Submodule.add_mem (shiftedSubmodule ℳ d.monoid p) hy hz
    · have hx : (x : L) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (Or.inl hn),
          Submodule.mem_bot] using x.property
      simp [hx]
  | add x z hx hz => simpa [add_lie] using Submodule.add_mem _ hx hz

/-- The shifted coefficient module with its restricted Lie action. -/
abbrev shiftedLieSubmodule : LieSubmodule R L M where
  toSubmodule := shiftedSubmodule ℳ d.monoid p
  lie_mem {x _} hy := d.lie_mem_shiftedSubmodule ℒ ℳ p x hy

/-- Forgetting the restricted Lie action recovers the shifted submodule. -/
@[simp]
theorem shiftedLieSubmodule_toSubmodule :
    (d.shiftedLieSubmodule ℒ ℳ p).toSubmodule = shiftedSubmodule ℳ d.monoid p := (rfl)

variable [DirectSum.Decomposition ℳ]

/-- The relative filtration on the shifted Lie module. Its carrier remembers the
restricted action, so filtered-action instances can be inferred. -/
abbrev shiftedLieFiltration : ModuleFiltration R (d.shiftedLieSubmodule ℒ ℳ p) :=
  d.shiftedFiltration ℳ p

/-- The restricted Lie action raises the relative coefficient filtration. -/
instance shiftedLieFiltration_isFiltrationRaising :
    IsFiltrationRaising d ℒ (d.shiftedLieFiltration ℒ ℳ p) where
  lie_mem {a b x y} hx hy := by
    classical
    rw [d.degreeSubmodule_def ℒ a] at hx
    refine Submodule.iSup_induction (fun n : {n : Γ // (a : ℤ) < d.degree n} => ℒ n)
      (motive := fun x =>
        ⁅x, y⁆ ∈ (d.shiftedLieFiltration ℒ ℳ p).submodule (a + b + 1)) hx ?_ (by simp) ?_
    · intro n x hx
      rw [d.mem_shiftedFiltration_iff ℳ p]
      intro q hq
      rw [LieSubmodule.coe_bracket]
      rw [← DirectSum.sum_support_decompose ℳ (y : M), lie_sum,
        DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : d.degree (m - p) < b
      · rw [(d.mem_shiftedFiltration_iff ℳ p).mp hy m hm, lie_zero,
          DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
      · apply DirectSum.decompose_of_mem_ne ℳ
          (SetLike.GradedBracket.bracket_mem hx (DirectSum.decompose ℳ (y : M) m).property)
        intro he
        have hd : d.degree (q - p) = d.degree n.val + d.degree (m - p) := by
          rw [← he, vadd_eq_add, add_sub_assoc, map_add]
        have := n.property
        omega
    · intro x z hx hz
      simpa [add_lie] using
        Submodule.add_mem ((d.shiftedLieFiltration ℒ ℳ p).submodule (a + b + 1)) hx hz

end Mei.PositiveDegrees
