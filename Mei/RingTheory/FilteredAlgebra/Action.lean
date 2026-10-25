/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.GroupTheory.CompletedGroup.Basic
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# Compatible actions on filtered algebra completions

Compatible actions of a group tower on the finite-order quotient algebras induce an action
of its completed group on the completed algebra. The action is a homomorphism to algebra
automorphisms, characterized by its projections. Every induced filtration ideal is invariant,
and a group element vanishing at an order acts trivially at that order.

The construction uses `AlgFiltration.liftₐ` for the compatible endomorphisms and Mathlib's
`MonoidHom.toHomUnits` and `AlgEquiv.algHomUnitsEquiv` to recover automorphisms. It needs no
surjectivity of the group transitions, separatedness of the original algebra, or assumption
that the actions arise from exponentials.
-/

public section

open CategoryTheory Opposite

universe u

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (F : AlgFiltration A) {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* ((A ⧸ F.ideal (k + 1)) ≃ₐ[R]
    (A ⧸ F.ideal (k + 1))))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : A ⧸ F.ideal (l + 1)),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (ρ l g x) =
      ρ k (G.map (homOfLE h).op g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) x))

private def actionEnd : completedGroup G →* (F.completion →ₐ[R] F.completion) where
  toFun g := F.liftₐ
    (fun k => (ρ k (CompletedGroup.projection k g)).toAlgHom.comp (F.projectionₐ k))
    (by
      intro k l h
      ext x
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, projectionₐ_apply]
      rw [Ideal.Quotient.factorₐ_apply, hρ h, CompletedGroup.map_projection,
        F.factor_projection h])
  map_one' := by
    apply AlgHom.ext
    intro x
    apply F.completion_ext
    intro k
    simp
  map_mul' g g' := by
    apply AlgHom.ext
    intro x
    apply F.completion_ext
    intro k
    simp

/-- Extend compatible quotient-algebra actions to an action of the completed group by
algebra automorphisms of the completed algebra. -/
def completedAction : completedGroup G →* (F.completion ≃ₐ[R] F.completion) :=
  (AlgEquiv.algHomUnitsEquiv R F.completion).toMonoidHom.comp (F.actionEnd ρ hρ).toHomUnits

/-- The action at order `k` depends only on the order-`k` group and algebra components. -/
@[simp]
theorem projection_completedAction (g : completedGroup G) (x : F.completion) (k : ℕ) :
    F.projection k (F.completedAction ρ hρ g x) =
      ρ k (CompletedGroup.projection k g) (F.projection k x) := by
  simp [completedAction, actionEnd]

/-- The projection formula uniquely determines the completed action. -/
theorem completedAction_unique (σ : completedGroup G →* (F.completion ≃ₐ[R] F.completion))
    (hσ : ∀ (g : completedGroup G) (x : F.completion) (k : ℕ),
      F.projection k (σ g x) = ρ k (CompletedGroup.projection k g) (F.projection k x)) :
    σ = F.completedAction ρ hρ := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply F.completion_ext
  intro k
  rw [F.projection_completedAction, hσ]

/-- Every completed automorphism preserves and reflects each filtration ideal. -/
@[simp]
theorem completedAction_mem_completionIdeal_iff (g : completedGroup G)
    (x : F.completion) (k : ℕ) :
    F.completedAction ρ hρ g x ∈ F.completionIdeal k ↔ x ∈ F.completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completionIdeal_succ, RingHom.mem_ker, F.projection_completedAction,
      map_eq_zero_iff _ (ρ k (CompletedGroup.projection k g)).injective]

/-- An element of the group filtration acts trivially through the corresponding order. -/
theorem projection_completedAction_of_mem_degreeFiltration {g : completedGroup G}
    {k : ℕ} (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.projection k (F.completedAction ρ hρ g x) = F.projection k x := by
  have hg' : CompletedGroup.projection k g = 1 := by
    simpa only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] using hg
  simp [hg']

/-- Elements vanishing through order `k` move every coefficient only in order `k + 1`. -/
theorem completedAction_sub_mem_completionIdeal {g : completedGroup G} {k : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.completedAction ρ hρ g x - x ∈ F.completionIdeal (k + 1) := by
  simp only [completionIdeal_succ, RingHom.mem_ker, map_sub,
    F.projection_completedAction_of_mem_degreeFiltration ρ hρ hg, sub_self]

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra S A] [IsScalarTower S R A]

/-- The completed action commutes with restriction of the coefficient scalars. -/
theorem completedAction_restrictScalars (g : completedGroup G) :
    (F.completedAction ρ hρ g).restrictScalars S =
      F.completedAction (R := S)
        (fun k => (AlgEquiv.restrictScalarsHom S).comp (ρ k))
        (by
          intro k l h g x
          simpa only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
            AlgEquiv.restrictScalars_apply] using hρ h g x) g := by
  apply AlgEquiv.ext
  intro x
  apply F.completion_ext
  intro k
  rw [AlgEquiv.restrictScalars_apply, F.projection_completedAction ρ hρ]
  symm
  convert F.projection_completedAction (R := S)
    (fun k => (AlgEquiv.restrictScalarsHom S).comp (ρ k))
    (by
      intro k l h g x
      simpa only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
        AlgEquiv.restrictScalars_apply] using hρ h g x) g x k
  simp only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
    AlgEquiv.restrictScalars_apply]

end RestrictScalars

end Mei.AlgFiltration
