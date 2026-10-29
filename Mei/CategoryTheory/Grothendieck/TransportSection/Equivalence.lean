/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck.TransportSection
public import Mei.CategoryTheory.Grothendieck.Pullback
public import Mathlib.CategoryTheory.Equivalence

/-!
# Transport presentations of sections

The transport presentation of a section is equivalent to the category of actual
sections of the Grothendieck projection. The comparison works for arbitrary
category-valued diagrams, including noninvertible transport arrows.

`ofSection` extracts transport data using `Grothendieck.liftFunctor` over the
identity base. `fromSectionHom` extracts vertical components, and its two
reconstruction equations identify the original comparison as fully faithful.
The explicit inverse functor `sectionInverseFunctor` extracts objects and
morphisms; object reconstruction supplies the unit and counit of `sectionEquivalence`.

For groupoid fibers, `sectionAutEquiv` transfers the existing compatible-family
description of transport automorphisms to automorphisms of actual sections.
-/

public section

open CategoryTheory

universe v u w z

namespace Mei.GrothendieckSection

variable {D : Type u} [Category.{v} D] {L : D ⥤ Cat.{w, z}}

/-- Normalize the base components of an actual section using the existing base lift. -/
private abbrev normalized (s : CategoryTheory.Grothendieck.Section L) : D ⥤ Grothendieck L :=
  Grothendieck.liftFunctor (𝟭 D) s.toFunctor s.toFunctor_comp_forget

/-- Normalizing an actual section preserves its underlying total functor. -/
private theorem normalized_eq (s : CategoryTheory.Grothendieck.Section L) :
    normalized s = s.toFunctor := by
  have h := Grothendieck.liftFunctor_comp_pre (𝟭 D) s.toFunctor s.toFunctor_comp_forget
  simpa only [Grothendieck.pre_id, Functor.comp_id] using h

/-- Transport data extracted from an actual section. -/
def ofSection (s : CategoryTheory.Grothendieck.Section L) : GrothendieckSection L where
  obj d := (normalized s).obj d |>.fiber
  map f := Grothendieck.fiberHom ((normalized s).map f) f
    (Grothendieck.liftHom_base _ _ _ _ _ _)
  map_id d := by
    simp only [(normalized s).map_id]
    -- The identity base lift stores its endpoints through the pullback diagram.
    -- Default transparency aligns them with the existing fiber extraction law.
    erw [Grothendieck.fiberHom_id (C := L) (d := d) ((normalized s).obj d).fiber]
  map_comp f g := by
    simp only [(normalized s).map_comp]
    -- As for identities, align the base-lift endpoints before using the fiber law.
    erw [Grothendieck.fiberHom_comp (C := L) ((normalized s).map f) ((normalized s).map g) f g
      (Grothendieck.liftHom_base _ _ _ _ _ _)
      (Grothendieck.liftHom_base _ _ _ _ _ _)]
    rfl

/-- The extracted transport data have the original section's underlying total functor. -/
@[simp]
theorem ofSection_toFunctor (s : CategoryTheory.Grothendieck.Section L) :
    (ofSection s).toFunctor = s.toFunctor := by
  trans normalized s
  · refine _root_.CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro d e f
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact Grothendieck.mk_fiberHom ((normalized s).map f) f
      (Grothendieck.liftHom_base _ _ _ _ _ _)
  · exact normalized_eq s

/-- Reassembling the extracted transport data recovers the actual section. -/
@[simp]
theorem toSection_ofSection (s : CategoryTheory.Grothendieck.Section L) :
    (ofSection s).toSection = s := by
  apply CategoryTheory.Functor.Fiber.fiberInclusion_obj_inj
  exact ofSection_toFunctor s

/-- Extracting transport data from its assembled section recovers the original data. -/
@[simp]
theorem ofSection_toSection (s : GrothendieckSection L) : ofSection s.toSection = s := by
  apply toFunctor_injective
  exact ofSection_toFunctor s.toSection

/-- The actual section and its transport presentation have the same arrow components. -/
private theorem toSection_toFunctor_map (s : GrothendieckSection L) {d e : D} (f : d ⟶ e) :
    s.toSection.toFunctor.map f = s.toFunctor.map f := (rfl)

/-- A component of a vertical section morphism, regarded in the actual fiber. -/
private def sectionHomComponent {s t : GrothendieckSection L} (α : s.toSection ⟶ t.toSection)
    (d : D) : s.obj d ⟶ t.obj d :=
  Grothendieck.verticalFiber ((CategoryTheory.Grothendieck.Section.hom α).app d)
    (sectionHom_base α d)

/-- Including the extracted component recovers the component of the section morphism. -/
@[simp↓]
private theorem ι_map_sectionHomComponent {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) (d : D) :
    (Grothendieck.ι L d).map (sectionHomComponent α d) =
      (CategoryTheory.Grothendieck.Section.hom α).app d :=
  Grothendieck.ι_map_verticalFiber _ (sectionHom_base α d)

/-- Naturality of a vertical label after factoring both transport arrows through
the target fiber inclusion. All endpoints are displayed as fiber objects. -/
private theorem sectionHom_factorized_naturality {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) {d e : D} (f : d ⟶ e) :
    ((Grothendieck.ιNatTrans f).app (s.obj d) ≫ (Grothendieck.ι L e).map (s.map f)) ≫
        (Grothendieck.ι L e).map (sectionHomComponent α e) =
      (Grothendieck.ι L d).map (sectionHomComponent α d) ≫
        (Grothendieck.ιNatTrans f).app (t.obj d) ≫ (Grothendieck.ι L e).map (t.map f) := by
  have h := (CategoryTheory.Grothendieck.Section.hom α).naturality f
  rw [toSection_toFunctor_map, toSection_toFunctor_map,
    ← ι_map_sectionHomComponent α d, ← ι_map_sectionHomComponent α e,
    toFunctor_map_factor, toFunctor_map_factor] at h
  -- The component equations identify the arrows. `Section.hom` still stores
  -- their endpoints through the fiber inclusion; default transparency identifies
  -- these with the explicit Grothendieck object constructors in the statement.
  exact h

/-- The fiber components of a vertical transformation between transport sections. -/
def fromSectionHom {s t : GrothendieckSection L} (α : s.toSection ⟶ t.toSection) : s ⟶ t where
  app d := Grothendieck.verticalFiber ((CategoryTheory.Grothendieck.Section.hom α).app d)
    (sectionHom_base α d)
  naturality {d e} f := by
    have h := sectionHom_factorized_naturality α f
    rw [Category.assoc, (Grothendieck.ιNatTrans f).naturality_assoc (sectionHomComponent α d),
      Functor.comp_map,
      ← Functor.map_comp, ← Functor.map_comp] at h
    rw [Grothendieck.ιNatTrans_app_comp_ι_map
      (⟨f, s.map f ≫ sectionHomComponent α e⟩ : s.toFunctor.obj d ⟶ t.toFunctor.obj e),
      Grothendieck.ιNatTrans_app_comp_ι_map
        (⟨f, (L.map f).toFunctor.map (sectionHomComponent α d) ≫ t.map f⟩ :
          s.toFunctor.obj d ⟶ t.toFunctor.obj e)] at h
    have hf := Grothendieck.congr h
    erw [eqToHom_refl, Category.id_comp] at hf
    exact hf.symm

/-- Extraction is computed by the vertical component in the fiber. -/
@[simp]
theorem fromSectionHom_app {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) (d : D) :
    (fromSectionHom α).app d =
      Grothendieck.verticalFiber ((CategoryTheory.Grothendieck.Section.hom α).app d)
        (sectionHom_base α d) := (rfl)

/-- Including an extracted fiber component recovers the original total component. -/
@[simp↓]
theorem ι_map_fromSectionHom_app {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) (d : D) :
    (Grothendieck.ι L d).map ((fromSectionHom α).app d) =
      (CategoryTheory.Grothendieck.Section.hom α).app d := by
  rw [fromSectionHom_app]
  exact Grothendieck.ι_map_verticalFiber _ (sectionHom_base α d)

/-- Reassembling the fiber components of a vertical transformation recovers it. -/
@[simp]
theorem toSectionHom_fromSectionHom {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) : toSectionHom (fromSectionHom α) = α := by
  apply CategoryTheory.Grothendieck.Section.hom_ext
  intro d
  rw [hom_toSectionHom, toNatTrans_app]
  exact Grothendieck.ι_map_verticalFiber _ (sectionHom_base α d)

instance : (sectionFunctor (L := L)).Full where
  map_surjective α := ⟨fromSectionHom α, toSectionHom_fromSectionHom α⟩

/-- Extracting the components of a transport morphism recovers that morphism. -/
@[simp]
theorem fromSectionHom_toSectionHom {s t : GrothendieckSection L} (α : s ⟶ t) :
    fromSectionHom (toSectionHom α) = α := by
  apply (sectionFunctor (L := L)).map_injective
  exact toSectionHom_fromSectionHom (toSectionHom α)

instance : (sectionFunctor (L := L)).EssSurj :=
  _root_.CategoryTheory.Functor.essSurj_of_surj (fun s => ⟨ofSection s, toSection_ofSection s⟩)

instance : (sectionFunctor (L := L)).IsEquivalence where

/-- The inverse comparison extracts transport data, including its morphisms.
The reconstruction equalities identify the endpoints before vertical extraction. -/
def sectionInverseFunctor : CategoryTheory.Grothendieck.Section L ⥤ GrothendieckSection L where
  obj := ofSection
  map {s t} α := fromSectionHom
    (eqToHom (toSection_ofSection s) ≫ α ≫ eqToHom (toSection_ofSection t).symm)
  map_id s := by
    apply (sectionFunctor (L := L)).map_injective
    rw [_root_.CategoryTheory.Functor.map_id]
    simp only [toSectionHom_fromSectionHom]
    simp
  map_comp α β := by
    apply (sectionFunctor (L := L)).map_injective
    rw [_root_.CategoryTheory.Functor.map_comp]
    simp only [toSectionHom_fromSectionHom]
    simp [Category.assoc]

/-- The inverse functor extracts the specified transport object. -/
@[simp]
theorem sectionInverseFunctor_obj (s : CategoryTheory.Grothendieck.Section L) :
    (sectionInverseFunctor (L := L)).obj s = ofSection s := (rfl)

/-- The inverse functor extracts the vertical transformation, with its endpoints
identified by the public object projection equations. -/
@[simp]
theorem sectionInverseFunctor_map {s t : CategoryTheory.Grothendieck.Section L} (α : s ⟶ t) :
    (sectionInverseFunctor (L := L)).map α =
      eqToHom (sectionInverseFunctor_obj s) ≫ fromSectionHom
        (eqToHom (toSection_ofSection s) ≫ α ≫ eqToHom (toSection_ofSection t).symm) ≫
          eqToHom (sectionInverseFunctor_obj t).symm := by
  dsimp only [sectionInverseFunctor]
  -- Only the bundled functor is unfolded. Its object projection equalities
  -- become reflexive; default transparency aligns these dependent endpoints.
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Extracting the assembled section recovers the transport object. -/
private theorem sectionInverseFunctor_obj_toSection (s : GrothendieckSection L) :
    (sectionInverseFunctor (L := L)).obj s.toSection = s := by
  rw [sectionInverseFunctor_obj, ofSection_toSection]

/-- Assembling an extracted section object recovers the actual section. -/
private theorem toSection_sectionInverseFunctor_obj (s : CategoryTheory.Grothendieck.Section L) :
    ((sectionInverseFunctor (L := L)).obj s).toSection = s := by
  rw [sectionInverseFunctor_obj, toSection_ofSection]

private theorem toSectionHom_eqToHom {s t : GrothendieckSection L} (h : s = t) :
    toSectionHom (eqToHom h) = eqToHom (congrArg toSection h) :=
  eqToHom_map sectionFunctor h

private theorem toSectionHom_comp {s t r : GrothendieckSection L}
    (α : s ⟶ t) (β : t ⟶ r) :
    toSectionHom (α ≫ β) = toSectionHom α ≫ toSectionHom β :=
  sectionFunctor.map_comp α β

/-- Fiberwise transport data and actual sections are equivalent categories.
The inverse is the explicit extraction functor; the unit and counit are the
isomorphisms given by the two object reconstruction equalities. -/
def sectionEquivalence : GrothendieckSection L ≌ CategoryTheory.Grothendieck.Section L where
  functor := sectionFunctor
  inverse := sectionInverseFunctor
  unitIso := NatIso.ofComponents (fun s => eqToIso (sectionInverseFunctor_obj_toSection s).symm) (by
    intro s t α
    apply (sectionFunctor (L := L)).map_injective
    rw [_root_.CategoryTheory.Functor.map_comp, _root_.CategoryTheory.Functor.map_comp]
    simp [toSectionHom_eqToHom, toSectionHom_comp, Category.assoc])
  counitIso := NatIso.ofComponents (fun s => eqToIso (toSection_sectionInverseFunctor_obj s)) (by
    intro s t α
    simp [toSectionHom_comp, toSectionHom_eqToHom, Category.assoc])
  functor_unitIso_comp s := by
    dsimp only [NatIso.ofComponents, eqToIso]
    rw [toSectionHom_eqToHom]
    simp

/-- The comparison equivalence uses the original transport-to-section functor. -/
@[simp]
theorem sectionEquivalence_functor : (sectionEquivalence (L := L)).functor = sectionFunctor := (rfl)

/-- The inverse object is the extracted transport datum, without a choice of preimage. -/
@[simp]
theorem sectionEquivalence_inverse_obj (s : CategoryTheory.Grothendieck.Section L) :
    (sectionEquivalence (L := L)).inverse.obj s = ofSection s := (rfl)

/-- The inverse map extracts the vertical transformation, transporting its
endpoints by the public inverse-object projection equations. -/
@[simp]
theorem sectionEquivalence_inverse_map {s t : CategoryTheory.Grothendieck.Section L}
    (α : s ⟶ t) : (sectionEquivalence (L := L)).inverse.map α =
      eqToHom (sectionEquivalence_inverse_obj s) ≫ fromSectionHom
        (eqToHom (toSection_ofSection s) ≫ α ≫ eqToHom (toSection_ofSection t).symm) ≫
          eqToHom (sectionEquivalence_inverse_obj t).symm := by
  simp only [sectionEquivalence, sectionInverseFunctor_map]

/-- The unit's target object is the original transport datum. -/
theorem sectionEquivalence_unit_obj (s : GrothendieckSection L) :
    ((sectionEquivalence (L := L)).functor ⋙ (sectionEquivalence (L := L)).inverse).obj s = s := by
  simp only [Functor.comp_obj, sectionEquivalence_functor, sectionEquivalence_inverse_obj,
    ofSection_toSection]

/-- The counit's source object is the original actual section. -/
theorem sectionEquivalence_counit_obj (s : CategoryTheory.Grothendieck.Section L) :
    ((sectionEquivalence (L := L)).inverse ⋙ (sectionEquivalence (L := L)).functor).obj s = s := by
  simp only [Functor.comp_obj, sectionEquivalence_functor, sectionEquivalence_inverse_obj,
    toSection_ofSection]

/-- The unit is the canonical equality isomorphism to the reconstructed object. -/
@[simp]
theorem sectionEquivalence_unitIso_hom_app (s : GrothendieckSection L) :
    (sectionEquivalence (L := L)).unitIso.hom.app s =
      eqToHom (sectionEquivalence_unit_obj s).symm := (rfl)

/-- The counit is the canonical equality isomorphism from the reconstructed object. -/
@[simp]
theorem sectionEquivalence_counitIso_hom_app (s : CategoryTheory.Grothendieck.Section L) :
    (sectionEquivalence (L := L)).counitIso.hom.app s =
      eqToHom (sectionEquivalence_counit_obj s) := (rfl)

/-- The inverse unit is the reverse equality isomorphism. -/
@[simp]
theorem sectionEquivalence_unitIso_inv_app (s : GrothendieckSection L) :
    (sectionEquivalence (L := L)).unitIso.inv.app s =
      eqToHom (sectionEquivalence_unit_obj s) := (rfl)

/-- The inverse counit is the reverse equality isomorphism. -/
@[simp]
theorem sectionEquivalence_counitIso_inv_app (s : CategoryTheory.Grothendieck.Section L) :
    (sectionEquivalence (L := L)).counitIso.inv.app s =
      eqToHom (sectionEquivalence_counit_obj s).symm := (rfl)

/-- The fully faithful comparison extracts the vertical components of a section morphism. -/
@[simp]
theorem sectionFunctor_preimage {s t : GrothendieckSection L}
    (α : s.toSection ⟶ t.toSection) :
    (sectionFunctor (L := L)).preimage α = fromSectionHom α := by
  apply (sectionFunctor (L := L)).map_injective
  rw [Functor.map_preimage, sectionFunctor_map, toSectionHom_fromSectionHom]

/-- Automorphisms of an actual section are compatible families of fiber
automorphisms, with conjugation by the extracted transport maps. -/
noncomputable def sectionAutEquiv [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L) :
    Aut s ≃* GrpCat.sectionsSubgroup (ofSection s).automorphismDiagram :=
  (Aut.autMulEquivOfIso (eqToIso (toSection_ofSection s).symm)).trans
    ((_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful
      (.ofFullyFaithful sectionFunctor) (ofSection s)).symm.trans
        (autEquivSections (ofSection s)))

/-- The compatible-family component is the vertical part of the original section
morphism, transported along object reconstruction. -/
@[simp]
theorem sectionAutEquiv_apply_hom [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L) (a : Aut s) (d : D) :
    ((sectionAutEquiv s a).val d).asIso.hom =
      (fromSectionHom (eqToHom (toSection_ofSection s) ≫ a.asIso.hom ≫
        eqToHom (toSection_ofSection s).symm)).app d := by
  have heval (b : Aut (ofSection s)) :
      ((evaluation d).mapAut _ b).asIso.hom = b.asIso.hom.app d := (rfl)
  simp only [sectionAutEquiv, MulEquiv.trans_apply, autEquivSections_apply, heval]
  -- The comparison functors store their object endpoints through fiber inclusions.
  -- Default transparency aligns those endpoints for Mathlib's component formula.
  erw [_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful_symm_apply_asIso_hom]
  simp [_root_.CategoryTheory.Functor.FullyFaithful.ofFullyFaithful]

/-- The inverse comparison includes the chosen family component, transported
back from the extracted section along object reconstruction. -/
@[simp]
theorem sectionAutEquiv_symm_apply_hom [∀ d, IsGroupoid (L.obj d)]
    (s : CategoryTheory.Grothendieck.Section L)
    (a : GrpCat.sectionsSubgroup (ofSection s).automorphismDiagram) (d : D) :
    (CategoryTheory.Grothendieck.Section.hom
      (((sectionAutEquiv s).symm a).asIso.hom)).app d =
      (CategoryTheory.Grothendieck.Section.hom
        (eqToHom (toSection_ofSection s).symm)).app d ≫
      (Grothendieck.ι L d).map ((a.val d).asIso.hom) ≫
      (CategoryTheory.Grothendieck.Section.hom
        (eqToHom (toSection_ofSection s))).app d := by
  have hconj (b : Aut (ofSection s).toSection) :
      ((Aut.autMulEquivOfIso (eqToIso (toSection_ofSection s).symm)).symm b).asIso.hom =
        (eqToHom (toSection_ofSection s).symm ≫ b.asIso.hom) ≫
          eqToHom (toSection_ofSection s) := by
    simp [Aut.autMulEquivOfIso, Category.assoc]
  simp only [sectionAutEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [hconj]
  -- Object reconstruction identifies endpoints through the section fiber inclusion;
  -- default transparency aligns these endpoints before applying the public formula.
  erw [_root_.CategoryTheory.Functor.FullyFaithful.autMulEquivOfFullyFaithful_apply_asIso_hom]
  simp only [CategoryTheory.Grothendieck.Section.hom_comp, NatTrans.comp_app]
  erw [hom_toSectionHom, toNatTrans_app,
    autEquivSections_symm_apply_hom, Category.assoc]
  rfl

end Mei.GrothendieckSection
