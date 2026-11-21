/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Filtered.Action
public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import Mei.LinearAlgebra.ModuleFiltration.Nilpotent

/-!
# Finite-order filtration-raising Lie actions on module filtrations

A filtration-raising action (`TauCeti.IsFiltrationRaising`) on the terms `F.submodule` of a
module filtration has the finite-order representations `PositiveDegrees.quotientLieAction` and
`PositiveDegrees.truncatedLieAction` from Tau Ceti. This file identifies them with the generic
filtration-raising quotient endomorphisms `ModuleFiltration.quotientRaisingEnd` and records
their compatibility with the quotient transitions `ModuleFiltration.transition`.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading IsFiltrationRaising)

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.ModuleFiltration

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [IsPositiveGrading d ℒ] [IsFiltrationRaising d ℒ F.submodule]

section Module

variable [DirectSum.Decomposition ℒ]

/-- The underlying endomorphism is the generic filtration-raising quotient map. -/
theorem quotientLieAction_eq_quotientRaisingEnd (k : ℕ) (x : L) :
    d.quotientLieAction ℒ F.submodule F.antitone k x =
      F.quotientRaisingEnd (LieModule.toEnd R L M x)
        (fun _ _ hm => d.lie_mem_succ ℒ F.submodule x hm) k := by
  apply LinearMap.ext
  intro a
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  exact (d.quotientLieAction_mk ℒ F.submodule F.antitone k x m).trans
    (F.quotientRaisingEnd_mk (LieModule.toEnd R L M x)
      (fun _ _ hm => d.lie_mem_succ ℒ F.submodule x hm) k m).symm

/-- Coefficient transitions intertwine the finite-order representations. -/
@[simp]
theorem transition_quotientLieAction {k l : ℕ} (h : k ≤ l) (x : L) (q : F.quotient l) :
    F.transition h (d.quotientLieAction ℒ F.submodule F.antitone l x q) =
      d.quotientLieAction ℒ F.submodule F.antitone k x (F.transition h q) := by
  rw [transition_eq_factor]
  exact d.factor_quotientLieAction ℒ F.submodule F.antitone h x q

end Module

section Lie

variable [GradedLieAlgebra ℒ]

/-- Lie and coefficient truncations commute with their finite-order actions. -/
@[simp]
theorem transition_truncatedLieAction {k l : ℕ} (h : k ≤ l)
    (x : d.truncatedLie ℒ l) (q : F.quotient l) :
    F.transition h (d.truncatedLieAction ℒ F.submodule F.antitone F.zero_eq_top l x q) =
      d.truncatedLieAction ℒ F.submodule F.antitone F.zero_eq_top k (d.truncationMap ℒ h x)
        (F.transition h q) := by
  rw [transition_eq_factor]
  exact d.factor_truncatedLieAction ℒ F.submodule F.antitone F.zero_eq_top h x q

end Lie

end Mei.ModuleFiltration
