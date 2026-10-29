/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Inner.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.CompletedLie

/-!
# Inner actions on completed enveloping algebras

The commutator with the canonical enveloping image gives an action of a Lie algebra
on its enveloping algebra by associative derivations. For a positive grading this action
raises the degree filtration. Its completed exponential action is conjugation by the
completed exponential of the canonical image.

The action is Mathlib's `LieRingModule.compLieHom` applied to the canonical map `ι`.
The instances are scoped to `UniversalEnvelopingAlgebra.InnerAction`: opening this
scope selects the commutator action, which differs from left multiplication on the
enveloping algebra. No PBW, freeness, or separatedness assumption is used.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UniversalEnvelopingAlgebra

open Mei Mei.UniversalEnvelopingAlgebra

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]

namespace InnerAction

/-- The commutator action pulled back along the canonical enveloping map. -/
scoped instance instLieRingModule : LieRingModule L (_root_.UniversalEnvelopingAlgebra R L) :=
  LieRingModule.compLieHom _ (ι R)

/-- The commutator action on the enveloping algebra is linear over the scalar ring. -/
scoped instance instLieModule : LieModule R L (_root_.UniversalEnvelopingAlgebra R L) :=
  LieModule.compLieHom _ (ι R)

/-- The inner action is the commutator with the canonical enveloping image. -/
@[simp]
theorem lie_eq (x : L) (a : _root_.UniversalEnvelopingAlgebra R L) :
    ⁅x, a⁆ = ι R x * a - a * ι R x := by
  rw [LieRingModule.compLieHom_apply, Ring.lie_def]

/-- The inner action satisfies the associative Leibniz rule. -/
scoped instance instIsDerivationAction :
    IsDerivationAction L (_root_.UniversalEnvelopingAlgebra R L) where
  lie_mul x a b := by simp [lie_eq, mul_sub, sub_mul, mul_assoc]

variable [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

/-- The inner action adds the Lie degree to the enveloping filtration order. -/
scoped instance instIsFiltrationRaising :
    IsFiltrationRaising d ℒ ((F).toModuleFiltration R) where
  lie_mem {a b x m} hx hm := by
    have hx' : x ∈ d.degreeIdeal ℒ a := by
      rw [← d.degreeIdeal_toSubmodule ℒ a] at hx
      exact hx
    have hi := ι_mem_degreeFiltration_of_mem_degreeIdeal d ℒ hx'
    rw [lie_eq]
    exact (F).ideal (a + b + 1) |>.sub_mem
      (by simpa only [Nat.add_assoc, Nat.add_comm 1] using (F).mul_mem hi hm)
      (by simpa only [Nat.add_comm b, Nat.add_assoc] using (F).mul_mem hm hi)

variable [Algebra ℚ R]

/-- Restrict the coefficient algebra along the rational structure on the scalar ring. -/
local instance rationalEnvelopingAlgebra : Algebra ℚ (_root_.UniversalEnvelopingAlgebra R L) :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- The exponential inner action on the completed enveloping algebra is conjugation
by the completed exponential of the canonical Lie image. -/
@[simp]
theorem expAction_apply (x : L) (a : (F).completion) :
    (F).expAction d ℒ x a =
      (F).completedExp ⟨(F).toCompletion (ι R x),
        ((F).toCompletion_mem_completionIdeal_iff 1 _).mpr
          (ι_mem_degreeFiltration_one ℒ d.degree
            (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn) x)⟩ * a *
      (F).completedExp (-⟨(F).toCompletion (ι R x),
        ((F).toCompletion_mem_completionIdeal_iff 1 _).mpr
          (ι_mem_degreeFiltration_one ℒ d.degree
            (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn) x)⟩) := by
  exact (F).expAction_apply_eq_completedExp_mul d ℒ x (ι R x) (lie_eq x)
    (ι_mem_degreeFiltration_one ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn) x) a

end InnerAction
end UniversalEnvelopingAlgebra
