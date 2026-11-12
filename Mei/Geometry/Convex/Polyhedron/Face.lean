/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Face

/-!
# Exposed faces of a half-space

The active-row description of polyhedral faces in TauCeti specializes to the
whole half-space or its boundary.
-/

public section

namespace IsExposed

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A nonempty exposed face of a half-space is either the entire half-space or the
boundary level. This includes constant affine functionals. -/
theorem eq_halfspace_or_zero {F : Set V} {g : V →ᴬ[ℝ] ℝ}
    (hF : IsExposed ℝ {x | g x ≤ 0} F) (hne : F.Nonempty) :
    F = {x | g x ≤ 0} ∨ F = {x | g x = 0} := by
  have hbase : {x | ∀ _ : Unit, g x ≤ 0} = {x | g x ≤ 0} := by simp
  rw [← hbase] at hF
  obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun _ : Unit => g) hne
  by_cases hmem : () ∈ I
  · right
    rw [hI]
    ext x
    constructor
    · rintro ⟨_, hx⟩
      exact hx () hmem
    · intro hx
      exact ⟨fun _ => hx.le, fun _ _ => hx⟩
  · left
    have hIempty : I = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hmem (Subsingleton.elim j () ▸ hj)
    simp only [hIempty, Finset.notMem_empty, IsEmpty.forall_iff, forall_const,
      and_true] at hI
    exact hI

end IsExposed
