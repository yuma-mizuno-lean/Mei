/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Sections of groupoid-valued diagrams

A section chooses an object in every fiber and compatible transport arrows. Morphisms
are fiberwise arrows commuting with transport. When the fibers are groupoids, so is
the category of sections.
Their automorphisms are precisely the compatible families of fiber automorphisms,
with transition given by transport followed by conjugation.

The total functor of a section lies strictly over the identity on the base. A represented
label diagram on the Grothendieck construction therefore gives a coefficient diagram
along each section. A morphism of sections induces an isomorphism of their limits,
computed on every projection by its represented fiber arrow.

The constructions use Mathlib's `Grothendieck.ι`, `Aut.autMulEquivOfIso`,
`Functor.mapAut`, `GrpCat.sectionsSubgroup` and `HasLimit.isoOfNatIso`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u w z v' u'

namespace Mei

/-- An object in each fiber of a category-valued diagram, with functorial transport. -/
@[ext]
structure GrothendieckSection {D : Type u} [Category.{v} D] (L : D ⥤ Cat.{w, z}) where
  /-- The chosen object in each fiber. -/
  obj (d : D) : L.obj d
  /-- Transport of the chosen object along a base arrow. -/
  map {d e : D} (f : d ⟶ e) : (L.map f).toFunctor.obj (obj d) ⟶ obj e
  /-- Transport along an identity is the canonical identification. -/
  map_id (d : D) : map (𝟙 d) = eqToHom (by simp)
  /-- Transport respects composition. -/
  map_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) :
    map (f ≫ g) = eqToHom (by simp) ≫ (L.map g).toFunctor.map (map f) ≫ map g

namespace GrothendieckSection

variable {D : Type u} [Category.{v} D] {L : D ⥤ Cat.{w, z}}

attribute [simp] map_id map_comp

/-- A vertical morphism between sections, commuting with the transport arrows. -/
@[ext]
structure Hom (s t : GrothendieckSection L) where
  /-- The arrow in each fiber. -/
  app (d : D) : s.obj d ⟶ t.obj d
  /-- Fiber arrows commute with transport. -/
  naturality {d e : D} (f : d ⟶ e) :
    (L.map f).toFunctor.map (app d) ≫ t.map f = s.map f ≫ app e

attribute [reassoc] Hom.naturality

/-- Sections and vertical morphisms form a category. -/
instance : Category (GrothendieckSection L) where
  Hom := Hom
  id s := ⟨fun d => 𝟙 (s.obj d), by simp⟩
  comp α β := ⟨fun d => α.app d ≫ β.app d, by
    intro d e f
    simp only [Functor.map_comp, Category.assoc]
    rw [β.naturality, α.naturality_assoc]⟩

@[simp]
theorem id_app (s : GrothendieckSection L) (d : D) : (𝟙 s : s ⟶ s).app d = 𝟙 _ := (rfl)

@[simp]
theorem comp_app {s t r : GrothendieckSection L} (α : s ⟶ t) (β : t ⟶ r) (d : D) :
    (α ≫ β).app d = α.app d ≫ β.app d := (rfl)

/-- Evaluation at a base object is a functor to that fiber. -/
abbrev evaluation (d : D) : GrothendieckSection L ⥤ L.obj d where
  obj s := s.obj d
  map α := α.app d

/-- The total functor associated to a section. -/
abbrev toFunctor (s : GrothendieckSection L) : D ⥤ Grothendieck L where
  obj d := ⟨d, s.obj d⟩
  map f := ⟨f, s.map f⟩
  map_id d := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [Grothendieck.id_fiber, map_id]
      -- The fiber lives in the category stored in `L.obj d`.
      erw [eqToHom_trans (C := L.obj d)]
  map_comp f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [Grothendieck.comp_fiber, map_comp]
      erw [eqToHom_trans_assoc (C := L.obj _)]

/-- The total functor of a section lies over the identity. -/
@[simp]
theorem toFunctor_comp_forget (s : GrothendieckSection L) :
    s.toFunctor ⋙ Grothendieck.forget _ = 𝟭 D := (rfl)

/-- A morphism of sections as a natural transformation of total functors. -/
def toNatTrans {s t : GrothendieckSection L} (α : s ⟶ t) : s.toFunctor ⟶ t.toFunctor where
  app d := (Grothendieck.ι _ d).map (α.app d)
  naturality d e f := by
    refine Grothendieck.ext _ _ (by simp [toFunctor]) ?_
    simp only [toFunctor, Grothendieck.ι, Grothendieck.comp_base, Grothendieck.comp_fiber,
      ← NatIso.naturality_2 (Cat.Hom.toNatIso (eqToIso (L.map_id e)) ≪≫
        eqToIso Cat.Hom.id_toFunctor), Functor.id_obj, Cat.Hom.id_toFunctor, eqToIso_refl,
      Iso.trans_refl, Cat.Hom.toNatIso_hom, eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans,
      eqToHom_app, Functor.id_map, Cat.Hom.toNatIso_inv, eqToIso.inv, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp, eqToHom_map,
      α.naturality]
    -- Normalize the remaining transports in the category stored in `L.obj e`.
    repeat erw [eqToHom_trans_assoc (C := L.obj e)]

@[simp]
theorem toNatTrans_app {s t : GrothendieckSection L} (α : s ⟶ t) (d : D) :
    (toNatTrans α).app d = (Grothendieck.ι _ d).map (α.app d) := (rfl)

/-- The category of sections maps to the functor category of the total category. -/
def totalFunctor : GrothendieckSection L ⥤ (D ⥤ Grothendieck L) where
  obj := toFunctor
  map := toNatTrans
  map_id s := by
    apply NatTrans.ext
    funext d
    exact (Grothendieck.ι _ d).map_id _
  map_comp α β := by
    apply NatTrans.ext
    funext d
    exact (Grothendieck.ι _ d).map_comp _ _

variable [∀ d, IsGroupoid (L.obj d)]

/-- A vertical morphism is inverted in every fiber. -/
noncomputable instance : Groupoid (GrothendieckSection L) where
  inv α := ⟨fun d => inv (α.app d), by
    intro d e f
    apply (cancel_mono (α.app e)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← α.naturality, ← Category.assoc, ← Functor.map_comp]
    simp⟩
  inv_comp α := by apply Hom.ext; funext d; simp
  comp_inv α := by apply Hom.ext; funext d; simp

@[simp]
theorem inv_app {s t : GrothendieckSection L} (α : s ⟶ t) (d : D) :
    (inv α).app d = inv (α.app d) := by
  rw [← Groupoid.inv_eq_inv α]
  rfl

/-- Fiber automorphisms transported along a section by conjugation. This is reducible
on objects, retaining the actual automorphism groups as carriers. -/
noncomputable abbrev automorphismDiagram (s : GrothendieckSection L) : D ⥤ GrpCat.{w} where
  obj d := GrpCat.of (Aut (s.obj d))
  map f := GrpCat.ofHom
    ((Aut.autMulEquivOfIso (asIso (s.map f))).toMonoidHom.comp ((L.map f).toFunctor.mapAut _))
  map_id d := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Aut.ext
    apply Iso.ext
    have h := Functor.congr_hom congr($(L.map_id d).toFunctor) a.asIso.hom
    simpa [Aut.autMulEquivOfIso, Functor.mapAut] using
      congrArg (fun k => inv (s.map (𝟙 d)) ≫ k ≫ s.map (𝟙 d)) h
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Aut.ext
    apply Iso.ext
    have h := Functor.congr_hom congr($(L.map_comp f g).toFunctor) a.asIso.hom
    simpa [Aut.autMulEquivOfIso, Functor.mapAut] using
      congrArg (fun k => inv (s.map (f ≫ g)) ≫ k ≫ s.map (f ≫ g)) h

/-- Transport acts on the underlying arrow by fiber transport followed by conjugation. -/
@[simp↓]
theorem automorphismDiagram_map_apply_hom (s : GrothendieckSection L)
    {d e : D} (f : d ⟶ e) (a : Aut (s.obj d)) :
    ((s.automorphismDiagram.map f) a).asIso.hom =
      inv (s.map f) ≫ (L.map f).toFunctor.map a.asIso.hom ≫ s.map f := (rfl)

/-- Automorphisms of a section are compatible families of fiber automorphisms. -/
noncomputable def autEquivSections (s : GrothendieckSection L) :
    Aut s ≃* GrpCat.sectionsSubgroup s.automorphismDiagram where
  toFun a := ⟨fun d => (evaluation d).mapAut s a, by
    intro d e f
    apply Aut.ext
    apply Iso.ext
    dsimp [Functor.mapAut, automorphismDiagram, Aut.autMulEquivOfIso]
    rw [a.asIso.hom.naturality, IsIso.inv_hom_id_assoc]⟩
  invFun a := Aut.of
    { hom := ⟨fun d => (a.val d).asIso.hom, by
        intro d e f
        have h := congrArg (fun a => s.map f ≫ a.asIso.hom) (a.property f)
        simpa using h⟩
      inv := ⟨fun d => (a.val d).asIso.inv, by
        intro d e f
        have h := congrArg (fun a => s.map f ≫ a.asIso.hom) ((a⁻¹).property f)
        simpa using h⟩
      hom_inv_id := by apply Hom.ext; funext d; simp
      inv_hom_id := by apply Hom.ext; funext d; simp }
  left_inv a := by
    apply Aut.ext
    apply Iso.ext
    apply Hom.ext
    rfl
  right_inv a := by apply Subtype.ext; funext d; rfl
  map_mul' a b := by apply Subtype.ext; funext d; exact ((evaluation d).mapAut s).map_mul a b

@[simp]
theorem autEquivSections_apply (s : GrothendieckSection L) (a : Aut s) (d : D) :
    (s.autEquivSections a).val d = (evaluation d).mapAut s a := (rfl)

/-- Reconstruction from compatible automorphisms retains their fiberwise arrows. -/
@[simp]
theorem autEquivSections_symm_apply_hom (s : GrothendieckSection L)
    (a : GrpCat.sectionsSubgroup s.automorphismDiagram) (d : D) :
    (s.autEquivSections.symm a).asIso.hom.app d = (a.val d).asIso.hom := (rfl)

section Coefficients

variable {V : Type u'} [Category.{v'} V] (A : Grothendieck L ⥤ V)
  {s t r : GrothendieckSection L}

/-- A completed label acts between the coefficient limits along its source and target sections. -/
noncomputable def completedLabelIso (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] :
    limit (s.toFunctor ⋙ A) ≅ limit (t.toFunctor ⋙ A) :=
  HasLimit.isoOfNatIso (Functor.isoWhiskerRight (totalFunctor.mapIso (asIso α)) A)

/-- Each projection computes the completed action using the represented fiber label. -/
@[reassoc (attr := simp)]
theorem completedLabelIso_hom_π (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] (d : D) :
    (completedLabelIso A α).hom ≫ limit.π (t.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (α.app d)) := by
  simp [completedLabelIso, totalFunctor]
  rfl

/-- The inverse completed action is computed using the inverse fiber label. -/
@[reassoc (attr := simp)]
theorem completedLabelIso_inv_π (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] (d : D) :
    (completedLabelIso A α).inv ≫ limit.π (s.toFunctor ⋙ A) d =
      limit.π (t.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (inv (α.app d))) := by
  simp [completedLabelIso, totalFunctor]
  rfl

/-- The identity label acts as the identity on the completed coefficient object. -/
@[simp]
theorem completedLabelIso_id (s : GrothendieckSection L) [HasLimit (s.toFunctor ⋙ A)] :
    completedLabelIso A (𝟙 s) = Iso.refl _ := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [completedLabelIso_hom_π]
  erw [(Grothendieck.ι L d).map_id, A.map_id, Category.comp_id (obj := V)]
  simp

/-- Completed labels act functorially. -/
@[simp]
theorem completedLabelIso_comp (α : s ⟶ t) (β : t ⟶ r)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)]
    [HasLimit (r.toFunctor ⋙ A)] :
    completedLabelIso A (α ≫ β) = completedLabelIso A α ≪≫ completedLabelIso A β := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  simp only [Iso.trans_hom, Category.assoc, completedLabelIso_hom_π,
    comp_app, Functor.map_comp]
  -- The fiber inclusion and total functor present the same objects through different wrappers.
  erw [A.map_comp, completedLabelIso_hom_π_assoc]
  exact (Category.assoc _ _ _).symm

/-- Inverting a label inverts its completed action. -/
@[simp]
theorem completedLabelIso_inv (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] :
    completedLabelIso A (inv α) = (completedLabelIso A α).symm := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [completedLabelIso_hom_π, Iso.symm_hom, completedLabelIso_inv_π, inv_app]

/-- The group of completed labels at a section acts on its completed coefficient object. -/
noncomputable def completedAut (s : GrothendieckSection L) [HasLimit (s.toFunctor ⋙ A)] :
    Aut s →* Aut (limit (s.toFunctor ⋙ A)) where
  toFun a := Aut.of (completedLabelIso A a.asIso.hom)
  map_one' := by apply Aut.ext; simp
  map_mul' a b := by apply Aut.ext; simp

/-- The action of a completed automorphism has its prescribed fiberwise projections. -/
@[reassoc (attr := simp)]
theorem completedAut_hom_π (s : GrothendieckSection L) [HasLimit (s.toFunctor ⋙ A)]
    (a : Aut s) (d : D) :
    (completedAut A s a).asIso.hom ≫ limit.π (s.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (a.asIso.hom.app d)) :=
  completedLabelIso_hom_π A a.asIso.hom d

end Coefficients

end GrothendieckSection
end Mei
