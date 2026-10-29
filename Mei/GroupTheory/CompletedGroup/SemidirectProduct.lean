/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.GroupTheory.CompletedGroup.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Completing semidirect products with a fixed acting group

Suppose a group `H` acts on each group of a tower, compatibly with its transitions.
The action extends to the completed group. Forming the semidirect product with `H`
commutes with completion, provided the transitions leave the `H` coordinate fixed.
The comparison and its inverse are characterized by their finite projections.
Thus a compatible family of transport labels, each consisting of a wall label and
a chart-change label, retains one chart-change label after completion.

The construction uses `CompletedGroup.lift` and Mathlib's `SemidirectProduct.map`.
No surjectivity of the tower transitions or finiteness of either group is required.
-/

public section

open CategoryTheory Opposite

universe u v

namespace Mei.CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}} {H : Type v} [Group H]
  (φ : ∀ j, H →* MulAut (F.obj j))
  (hφ : ∀ {j l} (f : j ⟶ l) (h : H) (x : F.obj j),
    F.map f (φ j h x) = φ l h (F.map f x))

private def actionHom (h : H) : completedGroup F →* completedGroup F :=
  lift (fun k => (φ (op k) h).toMonoidHom.comp (projection k)) (by
    intro k l hkl
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hφ, map_projection])

private theorem projection_actionHom (h : H) (x : completedGroup F) (k : ℕ) :
    projection k (actionHom φ hφ h x) = φ (op k) h (projection k x) := by
  rw [actionHom, projection_lift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- The compatible levelwise automorphisms give an action on the completed group. -/
def action : H →* MulAut (completedGroup F) where
  toFun h :=
    { toFun := actionHom φ hφ h
      map_mul' := (actionHom φ hφ h).map_mul
      invFun := actionHom φ hφ h⁻¹
      left_inv x := by
        apply ext
        intro k
        simp only [projection_actionHom, map_inv, MulAut.inv_apply_self]
      right_inv x := by
        apply ext
        intro k
        simp only [projection_actionHom, map_inv, MulAut.apply_inv_self] }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply ext
    intro k
    simp [projection_actionHom]
  map_mul' h h' := by
    apply MulEquiv.ext
    intro x
    apply ext
    intro k
    simp [projection_actionHom, MulAut.mul_apply]

/-- The completed action is computed by the action at each finite order. -/
@[simp]
theorem projection_action (h : H) (x : completedGroup F) (k : ℕ) :
    projection k (action φ hφ h x) = φ (op k) h (projection k x) :=
  projection_actionHom φ hφ h x k

/-- The tower of semidirect products, with transitions fixing the acting group. -/
abbrev semidirectTower : ℕᵒᵖ ⥤ GrpCat.{max u v} where
  obj j := GrpCat.of (F.obj j ⋊[φ j] H)
  map f := GrpCat.ofHom (SemidirectProduct.map (F.map f).hom (MonoidHom.id H)
    (fun h => by ext x; exact hφ f h x))
  map_id j := by
    ext x <;> simp
  map_comp f g := by
    ext x
    · exact ConcreteCategory.congr_hom (F.map_comp f g) x.left
    · rfl

/-- Projection from the completed semidirect product to one finite semidirect product. -/
def semidirectProjection (k : ℕ) :
    (completedGroup F ⋊[action φ hφ] H) →* F.obj (op k) ⋊[φ (op k)] H :=
  SemidirectProduct.map (projection k) (MonoidHom.id H)
    (fun h => by ext x; exact projection_action φ hφ h x k)

/-- The finite wall label is the corresponding projection of the completed wall label. -/
@[simp]
theorem semidirectProjection_left (k : ℕ) (x : completedGroup F ⋊[action φ hφ] H) :
    (semidirectProjection φ hφ k x).left = projection k x.left := (rfl)

/-- Projection retains the chart-change label. -/
@[simp]
theorem semidirectProjection_right (k : ℕ) (x : completedGroup F ⋊[action φ hφ] H) :
    (semidirectProjection φ hφ k x).right = x.right := (rfl)

private def assemble : (completedGroup F ⋊[action φ hφ] H) →*
    completedGroup (semidirectTower φ hφ) :=
  lift (semidirectProjection φ hφ) (by
    intro k l hkl
    ext x <;> simp)

private theorem projection_assemble (x : completedGroup F ⋊[action φ hφ] H) (k : ℕ) :
    projection k (assemble φ hφ x) = semidirectProjection φ hφ k x :=
  projection_lift _ _ k x

/-- All projections of a completed semidirect label have the same acting-group part. -/
theorem projection_right_eq_projection_zero (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    (projection k x).right = (projection 0 x).right := by
  have hx := congrArg SemidirectProduct.right (map_projection 0 k (Nat.zero_le k) x)
  simpa only [ConcreteCategory.hom_ofHom, SemidirectProduct.map_right,
    MonoidHom.id_apply] using hx

private def leftPart (x : completedGroup (semidirectTower φ hφ)) : completedGroup F :=
  ⟨fun k => (projection k x).left, (mem_completedGroup_iff F _).mpr (by
    intro k l hkl
    have hx := congrArg SemidirectProduct.left (map_projection k l hkl x)
    simpa only [ConcreteCategory.hom_ofHom, SemidirectProduct.map_left] using hx)⟩

private theorem projection_leftPart (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    projection k (leftPart φ hφ x) = (projection k x).left := by
  rw [projection_apply]
  rfl

/-- Completion commutes with semidirect product by a fixed acting group. The wall-label
coordinate is completed, while the acting-group coordinate is constant through the tower. -/
def semidirectProductEquiv : completedGroup (semidirectTower φ hφ) ≃*
    (completedGroup F ⋊[action φ hφ] H) where
  toFun x := ⟨leftPart φ hφ x, (projection 0 x).right⟩
  invFun := assemble φ hφ
  left_inv x := by
    apply ext
    intro k
    apply SemidirectProduct.ext
    · rw [projection_assemble φ hφ, semidirectProjection_left, projection_leftPart]
    · rw [projection_assemble, semidirectProjection_right]
      exact (projection_right_eq_projection_zero φ hφ x k).symm
  right_inv x := by
    apply SemidirectProduct.ext
    · apply ext
      intro k
      rw [projection_leftPart, projection_assemble φ hφ, semidirectProjection_left]
    · dsimp only
      rw [projection_assemble φ hφ, semidirectProjection_right]
  map_mul' x y := by
    apply SemidirectProduct.ext
    · apply ext
      intro k
      simp only [projection_leftPart, map_mul, SemidirectProduct.mul_left, projection_action]
      rw [projection_right_eq_projection_zero]
    · simp

/-- The first coordinate of the comparison is the compatible family of first coordinates. -/
@[simp]
theorem projection_semidirectProductEquiv_left
    (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    projection k (semidirectProductEquiv φ hφ x).left = (projection k x).left :=
  projection_leftPart φ hφ x k

/-- The fixed acting-group coordinate can be read at order zero. -/
@[simp]
theorem semidirectProductEquiv_right (x : completedGroup (semidirectTower φ hφ)) :
    (semidirectProductEquiv φ hφ x).right = (projection 0 x).right := (rfl)

/-- The inverse comparison reconstructs each finite transport label by projection. -/
@[simp]
theorem projection_semidirectProductEquiv_symm
    (x : completedGroup F ⋊[action φ hφ] H) (k : ℕ) :
    projection k ((semidirectProductEquiv φ hφ).symm x) =
      semidirectProjection φ hφ k x :=
  projection_assemble φ hφ x k

end Mei.CompletedGroup
