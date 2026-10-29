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

`fiberHom` extracts the fiber arrow when its base component is prescribed.
`verticalFiber` specializes this to a vertical arrow, and `ι_map_verticalFiber`
reconstructs it under the fiber inclusion.
-/

public section

namespace CategoryTheory.Grothendieck

universe v u w z

variable {D : Type u} [Category.{v} D] {C : D ⥤ Cat.{w, z}}

/-- The fiber arrow of a total arrow with a prescribed base component. -/
def fiberHom {d e : D} {x : C.obj d} {y : C.obj e}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨e, y⟩) (g : d ⟶ e) (h : f.base = g) :
    (C.map g).toFunctor.obj x ⟶ y :=
  eqToHom (by rw [h]) ≫ f.fiber

/-- Extracting an explicitly assembled arrow returns its fiber component. -/
@[simp]
theorem fiberHom_mk {d e : D} {x : C.obj d} {y : C.obj e}
    (g : d ⟶ e) (a : (C.map g).toFunctor.obj x ⟶ y) :
    fiberHom (⟨g, a⟩ : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨e, y⟩) g rfl = a := by
  simp [fiberHom]

/-- Reassembling the prescribed base and fiber recovers the total arrow. -/
@[simp]
theorem mk_fiberHom {d e : D} {x : C.obj d} {y : C.obj e}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨e, y⟩) (g : d ⟶ e) (h : f.base = g) :
    (⟨g, fiberHom f g h⟩ : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨e, y⟩) = f := by
  cases f
  subst g
  simp [fiberHom]

/-- A vertical total arrow as an arrow of its fiber. -/
def verticalFiber {d : D} {x y : C.obj d}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨d, y⟩) (h : f.base = 𝟙 d) : x ⟶ y :=
  eqToHom (by simp) ≫ fiberHom f (𝟙 d) h

/-- Fiber inclusion recovers the original vertical total arrow. -/
@[simp↓]
theorem ι_map_verticalFiber {d : D} {x y : C.obj d}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨d, y⟩) (h : f.base = 𝟙 d) :
    (ι C d).map (verticalFiber f h) = f := by
  conv_rhs => rw [← mk_fiberHom f (𝟙 d) h]
  refine Grothendieck.ext _ _ (by rfl) ?_
  dsimp [verticalFiber, fiberHom, ι]
  erw [eqToHom_trans_assoc (C := C.obj d), eqToHom_trans_assoc (C := C.obj d),
    eqToHom_trans_assoc (C := C.obj d)]

/-- Extracting an arrow included from a fiber returns the original fiber arrow. -/
@[simp↓]
theorem verticalFiber_ι_map {d : D} {x y : C.obj d} (a : x ⟶ y)
    (h : ((ι C d).map a).base = 𝟙 d) : verticalFiber ((ι C d).map a) h = a := by
  apply (ι C d).map_injective
  exact ι_map_verticalFiber _ h

/-- The fiber component of an identity is the diagram's identity identification. -/
@[simp]
theorem fiberHom_id {d : D} (x : C.obj d) :
    fiberHom (𝟙 (⟨d, x⟩ : Grothendieck C)) (𝟙 d) (id_base _) =
      eqToHom (by simp) := by
  dsimp only [fiberHom]
  erw [id_fiber, eqToHom_trans]

/-- Extracting the identity total arrow gives the identity arrow of its fiber. -/
@[simp]
theorem verticalFiber_id {d : D} (x : C.obj d) :
    verticalFiber (𝟙 (⟨d, x⟩ : Grothendieck C)) (id_base _) = 𝟙 x := by
  apply (ι C d).map_injective
  erw [ι_map_verticalFiber, Functor.map_id]
  rfl

/-- Extracting a composite of vertical arrows gives their fiber composite. -/
@[simp]
theorem verticalFiber_comp {d : D} {x y z : C.obj d}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨d, y⟩)
    (g : (⟨d, y⟩ : Grothendieck C) ⟶ ⟨d, z⟩)
    (hf : f.base = 𝟙 d) (hg : g.base = 𝟙 d) :
    verticalFiber (f ≫ g) (by simp only [comp_base, hf, hg, Category.id_comp]) =
      verticalFiber f hf ≫ verticalFiber g hg := by
  apply (ι C d).map_injective
  have h := (ι C d).map_comp (verticalFiber f hf) (verticalFiber g hg)
  erw [ι_map_verticalFiber, ι_map_verticalFiber] at h
  exact (ι_map_verticalFiber _ _).trans h.symm

/-- Fiber extraction of a composite transports the first fiber arrow and then
composes with the second, after the diagram's canonical composition identification. -/
@[simp]
theorem fiberHom_comp {d e b : D} {x : C.obj d} {y : C.obj e} {z : C.obj b}
    (f : (⟨d, x⟩ : Grothendieck C) ⟶ ⟨e, y⟩)
    (g : (⟨e, y⟩ : Grothendieck C) ⟶ ⟨b, z⟩)
    (a : d ⟶ e) (c : e ⟶ b) (hf : f.base = a) (hg : g.base = c) :
    fiberHom (f ≫ g) (a ≫ c) (by simp only [comp_base, hf, hg]) =
      eqToHom (by simp) ≫ (C.map c).toFunctor.map (fiberHom f a hf) ≫ fiberHom g c hg := by
  cases f
  cases g
  subst a
  subst c
  simp only [fiberHom, comp_fiber, eqToHom_refl, Category.id_comp]
  erw [eqToHom_trans_assoc]

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

/-- Successive canonical transports agree with transport along the composite after identifying
the iterated image with the image of the composite in the target fiber. -/
theorem ιNatTrans_app_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) (x : C.obj d) :
    (ιNatTrans f).app x ≫ (ιNatTrans g).app ((C.map f).toFunctor.obj x) ≫
      (ι C b).map (eqToHom (by simp)) = (ιNatTrans (f ≫ g)).app x := by
  let h : (⟨e, (C.map f).toFunctor.obj x⟩ : Grothendieck C) ⟶
      ⟨b, (C.map (f ≫ g)).toFunctor.obj x⟩ :=
    ⟨g, eqToHom (by simp)⟩
  rw [ιNatTrans_app_comp_ι_map h]
  symm
  refine Grothendieck.ext _ _ (by
    dsimp [Grothendieck.ιNatTrans, Grothendieck.comp, h]
    rfl) ?_
  dsimp [Grothendieck.ιNatTrans, Grothendieck.ι, h]
  erw [(C.map g).toFunctor.map_id]
  erw [Category.comp_id (obj := C.obj b), Category.id_comp (obj := C.obj b),
    eqToHom_trans (C := C.obj b)]
  rfl

end CategoryTheory.Grothendieck

namespace CategoryTheory.Grothendieck

variable {D : Type*} [Category* D] {C : D ⥤ Cat}

/-- A morphism of a Grothendieck construction is invertible if its base and fiber
morphisms are invertible. -/
instance isIso_of_base_fiber {X Y : Grothendieck C} (f : X ⟶ Y)
    [IsIso f.base] [IsIso f.fiber] : IsIso f := by
  exact (isoMk (asIso f.base) (asIso f.fiber)).isIso_hom

end CategoryTheory.Grothendieck
