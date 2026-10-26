/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.GroupAction

/-!
# Comparing concrete and categorical completion actions

Compatible group actions on a filtered module's quotient tower give natural
isomorphisms of that tower. Taking their limits recovers the existing action on
the concrete compatible-family completion, through the canonical limit comparison.
Thus a categorical coefficient-limit action can be computed on actual completed
module elements and their finite quotient components.

The construction uses Mathlib's `NatIso.ofComponents` and
`HasLimit.isoOfNatIso`, and the universal property
`Mei.ModuleFiltration.completionIsLimit`.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Mei.ModuleFiltration

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) {G : ℕᵒᵖ ⥤ GrpCat.{w}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* (F.quotient k ≃ₗ[R] F.quotient k))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : F.quotient l),
    F.transition h (ρ l g x) = ρ k (G.map (homOfLE h).op g) (F.transition h x))

/-- A completed group label acts by a natural automorphism of the quotient tower. -/
def quotientAction (g : completedGroup G) : F.quotientTower ≅ F.quotientTower :=
  NatIso.ofComponents (fun k => (ρ k.unop (CompletedGroup.projection k.unop g)).toModuleIso)
    (by
      intro k l f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      -- Expose the quotient tower's concrete transition and the component linear maps.
      change ρ l.unop (CompletedGroup.projection l.unop g)
          (F.transition (leOfHom f.unop) x) =
        F.transition (leOfHom f.unop) (ρ k.unop (CompletedGroup.projection k.unop g) x)
      simpa only [CompletedGroup.map_projection] using
        (hρ (leOfHom f.unop) (CompletedGroup.projection k.unop g) x).symm)

/-- Each component of the tower automorphism is the prescribed finite representation. -/
@[simp]
theorem quotientAction_hom_app (g : completedGroup G) (k : ℕᵒᵖ) :
    (F.quotientAction ρ hρ g).hom.app k =
      ModuleCat.ofHom (ρ k.unop (CompletedGroup.projection k.unop g)).toLinearMap := (rfl)

/-- The inverse tower action uses the inverse finite linear automorphism. -/
@[simp]
theorem quotientAction_inv_app (g : completedGroup G) (k : ℕᵒᵖ) :
    (F.quotientAction ρ hρ g).inv.app k =
      ModuleCat.ofHom (ρ k.unop (CompletedGroup.projection k.unop g)).symm.toLinearMap := (rfl)

/-- The identity completed label acts identically on the quotient diagram. -/
@[simp]
theorem quotientAction_one : F.quotientAction ρ hρ 1 = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  simp
  rfl

/-- Multiplication acts in function-composition order on the quotient diagram. -/
@[simp]
theorem quotientAction_mul (g h : completedGroup G) :
    F.quotientAction ρ hρ (g * h) =
      F.quotientAction ρ hρ h ≪≫ F.quotientAction ρ hρ g := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp
  rfl

/-- Inversion of a completed label inverts its natural quotient action. -/
@[simp]
theorem quotientAction_inv (g : completedGroup G) :
    F.quotientAction ρ hρ g⁻¹ = (F.quotientAction ρ hρ g).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp

/-- Taking the limit of the quotient action agrees with the concrete completion action. -/
theorem completedAction_completionIsoLimit (g : completedGroup G) :
    (F.completedAction ρ hρ g).toModuleIso ≪≫ F.completionIsoLimit =
      F.completionIsoLimit ≪≫ HasLimit.isoOfNatIso (F.quotientAction ρ hρ g) := by
  apply Iso.ext
  apply limit.hom_ext
  intro k
  simp only [Iso.trans_hom, Category.assoc]
  -- The tower objects and the concrete quotient modules have different wrappers.
  erw [completionIsoLimit_hom_π, HasLimit.isoOfNatIso_hom_π,
    completionIsoLimit_hom_π_assoc]
  rw [quotientAction_hom_app]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  -- Evaluate the categorical composites as linear maps on the concrete completion.
  change F.projection k.unop (F.completedAction ρ hρ g x) =
    ρ k.unop (CompletedGroup.projection k.unop g) (F.projection k.unop x)
  exact F.projection_completedAction ρ hρ g x k.unop

end Mei.ModuleFiltration
