/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Grothendieck

/-!
# Factoring morphisms in a Grothendieck construction

Every morphism factors as the canonical transport from its source to the target fiber,
followed by a morphism in that fiber. This relates Mathlib's `Grothendieck.ιNatTrans`
and fiber inclusions `Grothendieck.ι` to arbitrary morphisms, allowing cone equations
on the total category to be checked fiberwise.
-/

public section

namespace CategoryTheory.Grothendieck

universe v u w z

variable {D : Type u} [Category.{v} D] {C : D ⥤ Cat.{w, z}}

/-- A morphism is canonical transport followed by its fiber morphism. -/
theorem ιNatTrans_app_comp_ι_map {X Y : Grothendieck C} (h : X ⟶ Y) :
    (ιNatTrans h.base).app X.fiber ≫ (ι C Y.base).map h.fiber = h := by
  cases X with | mk d x =>
  cases Y with | mk e y =>
  dsimp [Grothendieck.ιNatTrans, Grothendieck.ι]
  refine Grothendieck.ext _ _ (by simp [Grothendieck.comp_base]) ?_
  -- Retype the fiber composite after expanding the dependent inclusion maps.
  change (eqToHom _ ≫ eqToHom _ ≫ (C.map (𝟙 e)).toFunctor.map (𝟙 _) ≫
    eqToHom _ ≫ h.fiber : (C.map h.base).toFunctor.obj x ⟶ y) = h.fiber
  simp only [comp_base, Functor.map_id, Category.id_comp, eqToHom_trans_assoc]
  erw [eqToHom_trans_assoc (C := C.obj e)]
  erw [eqToHom_refl (C := C.obj e), Category.id_comp (obj := C.obj e)]

end CategoryTheory.Grothendieck
