/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.SingleObj

/-!
# Evaluation in one-object Grothendieck constructions

An automorphism of a one-object group evaluates to its group element, and
inclusion from a fiber preserves the label.
-/

public section

open CategoryTheory

universe v u w

namespace Units

/-- The automorphism of the unique object given by a group element has that element as arrow. -/
theorem toAut_toUnits_asIso_hom {G : Type*} [Group G] (x : G) :
    (Units.toAut G (toUnits x)).asIso.hom = x := by
  simp [SingleObj.toEnd_def]

end Units

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})

/-- Fiber inclusion retains its group element. -/
@[simp]
theorem singleObjFiber_ι_map (d : D) (g : F.obj d) :
    F.singleObjFiber ((Grothendieck.ι (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) d).map
      (X := SingleObj.star (F.obj d)) (Y := SingleObj.star (F.obj d)) g) = g := by
  simp [singleObjFiber_def, Grothendieck.ι, SingleObj.comp_as_mul (F.obj d),
    SingleObj.id_as_one (F.obj d)]

end CategoryTheory.Functor
