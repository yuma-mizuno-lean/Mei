/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Truncation
public import Mei.Algebra.PositiveDegrees.Grading

/-!
# Degree bounds for Lie algebra truncations

The homogeneous pieces of a truncation vanish beyond its cutoff. These lemmas
express that bound using degree ideals and the finite set of retained degrees.
-/

public section

namespace TauCeti.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The truncation map is the quotient transition for the decreasing degree ideals. -/
theorem truncationMap_eq_factor {k l : ℕ} (h : k ≤ l) :
    d.truncationMap ℒ h = LieIdeal.factor (d.degreeIdeal_antitone ℒ h) := by
  apply (d.degreeIdeal ℒ l).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- A degree truncation has no terms above its retained cutoff. -/
@[simp]
theorem degreeIdeal_truncatedGrading_eq_bot {k l : ℕ} (hkl : k ≤ l) :
    d.degreeIdeal (d.truncatedGrading ℒ k) l = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [degreeIdeal_toSubmodule, degreeSubmodule_def]
  exact iSup_eq_bot.mpr fun n =>
    d.truncatedGrading_eq_bot ℒ (lt_of_le_of_lt (by exact_mod_cast hkl) n.property)

/-- A nonzero piece in a truncation has nonzero allowed degree below the cutoff. -/
theorem mem_cutoff_of_truncatedGrading_ne_bot {k : ℕ} {n : N}
    (hn : d.truncatedGrading ℒ k n ≠ ⊥) : n ∈ d.cutoff k \ {0} := by
  have hp : n ∈ d.monoid ∧ n ≠ 0 := by
    by_contra h
    exact hn (IsPositiveGrading.eq_bot (d := d) (ℒ := d.truncatedGrading ℒ k) n (by tauto))
  refine ⟨d.mem_cutoff.mpr ⟨hp.1, ?_⟩, hp.2⟩
  exact le_of_not_gt (fun h => hn (d.truncatedGrading_eq_bot ℒ h))

end TauCeti.PositiveDegrees
