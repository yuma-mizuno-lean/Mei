/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Support
public import Mei.LinearAlgebra.GradedModule.History.Erasure

/-!
# Unchanged-degree encounters in finite BCH histories

In the inherited grading of a finite shifted coefficient module, the diagonal
component of every BCH wall action is the identity. Consequently an encounter
which leaves the degree unchanged also leaves the entire decoration unchanged.
A history with constant degree carries its incoming decoration on every segment,
even when the wall labels themselves are nontrivial or inverted.
Omitting an unchanged-degree propagation factor preserves the final weight;
this contracts coefficient histories without altering geometric encounter data.

The diagonal calculation uses
`PositiveDegrees.shiftedQuotientComponent_truncatedBCHAction_of_mem_same`,
transported to the inherited quotient grading. Segment decorations are the
existing `homogeneousHistoryStage`, with the incoming segment indexed last.
These whole-component propagation rules are those of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Definition 2.10
and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "G(" k ")" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)

/-- At an encounter whose two recorded degrees coincide, the whole finite BCH
history decoration is unchanged. This includes the first encounter and does not
require that the final decoration survive. -/
theorem homogeneousHistoryStage_truncatedBCHAction_eq_of_degree_eq
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : G(k) r₀) (j : Fin n)
    (hj : r j = Fin.snoc (α := fun _ => Γ) r r₀ j.succ) :
    homogeneousHistoryStage G(k)
        (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r j.castSucc a =
      homogeneousHistoryStage G(k)
        (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r j.succ a :=
  homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self
    (fun j _ _ hx => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g j) hx) r a.property j hj

/-- An unchanged-degree BCH propagation factor can be omitted when computing
the final weight. All other labels and selected degrees retain their order;
this statement concerns coefficient histories, not the encounters of a path. -/
theorem homogeneousHistory_truncatedBCHAction_removeNth
    (k : ℕ) {n : ℕ} (g : Fin (n + 1) → d.truncatedGroup ℒ k)
    (r : Fin (n + 1) → Γ) (r₀ : Γ) (a : G(k) r₀) (j : Fin (n + 1))
    (hj : r j = Fin.snoc (α := fun _ => Γ) r r₀ j.succ) :
    homogeneousHistory G(k)
        (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a =
      homogeneousHistory G(k)
        (fun i => ((F).truncatedBCHAction d ℒ k (j.removeNth g i)).toLinearMap)
        (j.removeNth r) a :=
  homogeneousHistory_removeNth G(k) _ r a j
    (d.homogeneousHistoryStage_truncatedBCHAction_eq_of_degree_eq ℒ ℳ p k g r r₀ a j hj)

/-- Every segment of a constant-degree BCH history carries exactly its incoming
decoration, independently of all labels and of the number of encounters. -/
@[simp↓]
theorem homogeneousHistoryStage_truncatedBCHAction_const
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Γ) (a : G(k) r) (j : Fin (n + 1)) :
    homogeneousHistoryStage G(k)
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) (fun _ => r) j a = a :=
  homogeneousHistoryStage_const_of_decompose_self
    (fun j _ hx => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g j) hx) a.property j

/-- A constant-degree finite BCH history fixes its incoming decoration,
independently of all labels and of the number of encounters. -/
@[simp↓]
theorem homogeneousHistory_truncatedBCHAction_const
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Γ) (a : G(k) r) :
    homogeneousHistory G(k)
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) (fun _ => r) a = a :=
  homogeneousHistory_const_of_decompose_self
    (fun j _ hx => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g j) hx) a.property

end Mei.PositiveDegrees
