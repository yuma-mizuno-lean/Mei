/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient

/-!
# Module filtration completions and quotient-tower limits

The order quotients of a module filtration identify with the terms of
TauCeti's quotient tower. These equivalences identify compatible families
and commute with the projections from the resulting completion.
-/

public section

open Opposite TauCeti

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M)

/-- The shifted submodule family decreases with the quotient order. -/
theorem quotientAntitone : Antitone (fun k => F.submodule (k + 1)) :=
  fun _ _ h => F.antitone (Nat.add_le_add_right h 1)

local notation "J" => fun k => F.submodule (k + 1)
local notation "T" => ModuleTower.quotients J (quotientAntitone F)

/-- The order quotient and the corresponding term of the quotient tower are equivalent. -/
def quotientEquivTower (k : ℕ) : F.quotient k ≃ₗ[R] (T).obj (op k) := by
  let f := (F.submodule (k + 1)).liftQ (ModuleTower.quotientsπ J (quotientAntitone F) k)
    (by rw [ModuleTower.ker_quotientsπ])
  let g := ModuleTower.quotientsLift J (quotientAntitone F) k (F.submodule (k + 1)).mkQ
    (by rw [Submodule.ker_mkQ])
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply ModuleTower.quotients_hom_ext J (quotientAntitone F)
    apply LinearMap.ext
    intro x
    simp [f, g, Submodule.liftQ_apply]
  · apply Submodule.linearMap_qext (F.submodule (k + 1))
    apply LinearMap.ext
    intro x
    simp [f, g, Submodule.liftQ_apply]

/-- The term equivalence sends a quotient class to the canonical tower projection. -/
@[simp]
theorem quotientEquivTower_mk (k : ℕ) (x : M) :
    quotientEquivTower F k (Submodule.Quotient.mk x) =
      ModuleTower.quotientsπ J (quotientAntitone F) k x := by
  exact Submodule.liftQ_apply _ _ x

/-- The term equivalences commute with the quotient transitions. -/
theorem quotientEquivTower_transition {k l : ℕ} (h : k ≤ l) (x : F.quotient l) :
    (T).transitionOfLE h (quotientEquivTower F l x) =
      quotientEquivTower F k (F.transition h x) := by
  obtain ⟨x, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp

/-- The filtration completion is linearly equivalent to the limit of its quotient tower. -/
def completionEquivTowerLimit : F.completion ≃ₗ[R] (T).lim where
  toFun x := ⟨fun k => quotientEquivTower F k (F.projection k x),
    (T).mem_lim.mpr fun k => by
      rw [← ModuleTower.transitionOfLE_succ, quotientEquivTower_transition,
        F.transition_projection]⟩
  invFun y := ⟨fun k => (quotientEquivTower F k.unop).symm ((T).limπ k.unop y),
    (F.mem_completionSubmodule_iff _).mpr fun k l h => by
      apply (quotientEquivTower F k).injective
      -- The two evaluations of the inverse family reduce to the inverse quotient maps
      -- applied to the corresponding limit projections.
      change quotientEquivTower F k (F.transition h
        ((quotientEquivTower F l).symm ((T).limπ l y))) =
        quotientEquivTower F k ((quotientEquivTower F k).symm ((T).limπ k y))
      rw [← quotientEquivTower_transition, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      simpa only [ModuleTower.limπ_apply] using (T).transitionOfLE_coe_lim y h⟩
  left_inv x := by
    apply F.completion_ext
    intro k
    simp [ModuleTower.limπ_apply]
  right_inv y := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]
  map_add' x y := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]
  map_smul' r x := by
    apply (T).lim_ext
    intro k
    simp [ModuleTower.limπ_apply]

/-- A projection of the limit equivalence is the corresponding term equivalence. -/
theorem limπ_completionEquivTowerLimit (k : ℕ) (x : F.completion) :
    (T).limπ k (completionEquivTowerLimit F x) = quotientEquivTower F k (F.projection k x) := by
  rw [ModuleTower.limπ_apply]
  rfl

end Mei.ModuleFiltration
