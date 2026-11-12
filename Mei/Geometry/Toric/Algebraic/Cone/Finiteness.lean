/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone.Finiteness

/-!
# Finite tests for lattice points in rational cones

A finite generating family of the dual semigroup tests membership at every
lattice point.
-/

public section

namespace Mei.Toric

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Finitely many integral characters nonnegative on a lattice-rational cone
test membership of all lattice points in that cone. -/
theorem exists_finset_dualSemigroup_mem_iff (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) :
    ∃ s : Finset (N →+ ℤ), (∀ m ∈ s, m ∈ dualSemigroup hi σ) ∧
      ∀ n, i n ∈ σ ↔ ∀ m ∈ s, 0 ≤ m n := by
  obtain ⟨s, hs⟩ := AddSubmonoid.isAddFG_iff.mp
    ((AddMonoid.fg_iff_addSubmonoid_fg _).mp (hσ.fg_dualSemigroup hi))
  refine ⟨s, fun m hm => hs ▸ AddSubmonoid.subset_closure hm, fun n => ?_⟩
  rw [hσ.mem_iff_forall_dualSemigroup_nonneg hi]
  constructor
  · exact fun hn m hm => hn m (hs ▸ AddSubmonoid.subset_closure hm)
  · intro hn m hm
    rw [← hs] at hm
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact hn m hm
    | zero => simp
    | add a b ha hb iha ihb => simpa using add_nonneg iha ihb

end Mei.Toric
