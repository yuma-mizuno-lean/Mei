/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.CategoryTheory.Grothendieck.TransportSection
public import Mei.GroupTheory.CompletedGroup.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Group diagrams as one-object label systems

A diagram of groups gives a diagram of one-object groupoids. Its distinguished
section uses identity transport. Automorphisms of this section are exactly
compatible group elements; for a tower these are the existing completed group.
Thus the section interpretation of labels retains their multiplication and their
finite-order components, including ordered products and changes of cutoff.

The construction uses Mathlib's `MonCat.toCat`, `Units.toAut` and `toUnits`,
and `GrothendieckSection.autEquivSections` for compatible automorphisms.
The representation specializes the formula of Mathlib's `Grothendieck.functorFrom`.
Its restriction recovers the original coefficient diagram, and the induced section
label action is the unique action on its limit with the given levelwise formula.
-/

public section

open CategoryTheory CategoryTheory.Limits Mei Opposite

universe u v w

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})

/-- The identity-transport section of the associated one-object groupoids. This is an
abbreviation so its fiber objects retain their original single-object types. -/
abbrev singleObjSection :
    GrothendieckSection (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) where
  obj d := SingleObj.star (F.obj d)
  map {d e} _ := (1 : F.obj e)
  map_id _ := by simp [MonCat.toCat, SingleObj.id_as_one]; rfl
  map_comp {d e b} _ _ := by
    simp only [MonCat.toCat, comp_obj, comp_map, eqToHom_refl, Category.id_comp,
      toCatHom_toFunctor, SingleObj.mapHom_apply_map, map_one]
    exact (mul_one (1 : F.obj b)).symm

@[simp]
theorem singleObjSection_obj (d : D) :
    F.singleObjSection.obj d = SingleObj.star (F.obj d) := (rfl)

@[simp]
theorem singleObjSection_map {d e : D} (f : d ⟶ e) :
    F.singleObjSection.map f = (1 : F.obj e) := (rfl)

/-- The fibers of a group diagram are groupoids. -/
local instance singleObjDiagramIsGroupoid :
    ∀ d, IsGroupoid ((F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat).obj d) :=
  fun d => inferInstanceAs (IsGroupoid (SingleObj (F.obj d)))

/-- Compatible group elements are precisely automorphisms of the identity-transport section. -/
noncomputable def singleObjSectionAutEquiv :
    GrpCat.sectionsSubgroup F ≃* Aut F.singleObjSection where
  toFun g := F.singleObjSection.autEquivSections.symm
    ⟨fun d => Units.toAut (F.obj d) (toUnits (g.val d)), by
      intro d e f
      apply Aut.ext
      apply Iso.ext
      -- Expose the forgotten group homomorphism so the transport formula can rewrite it.
      change ((F.singleObjSection.automorphismDiagram.map f)
        (Units.toAut (F.obj d) (toUnits (g.val d)))).asIso.hom = _
      rw [GrothendieckSection.automorphismDiagram_map_apply_hom]
      simp only [MonCat.toCat, comp_obj, Cat.of_α, singleObjSection, comp_map,
        toCatHom_toFunctor, SingleObj.mapHom_apply_obj, id_eq,
        SingleObj.inv_as_inv (F.obj e), inv_one, Units.toAut_apply_asIso_hom,
        SingleObj.toEnd, End.homEquiv, Equiv.symm_mk, val_toUnits_apply,
        MulEquiv.coe_mk, Equiv.coe_fn_mk, SingleObj.mapHom_apply_map,
        GrpCat.forget₂_map, SingleObj.comp_as_mul (F.obj e),
        @one_mul (F.obj e) _, @mul_one (F.obj e) _]
      convert g.property f using 1
      rfl⟩
  invFun a := ⟨fun d => a.asIso.hom.app d, by
    intro d e f
    -- Name the underlying family to keep group operations independent of fiber wrappers.
    let b : ∀ d, F.obj d := fun d => a.asIso.hom.app d
    have ht : (1 : F.obj e) * (F.map f) (b d) = b e * 1 := a.asIso.hom.naturality f
    simp only [one_mul, mul_one] at ht
    convert ht using 1
    rfl⟩
  left_inv g := by
    apply Subtype.ext
    funext d
    dsimp only
    rw [GrothendieckSection.autEquivSections_symm_apply_hom]
    rfl
  right_inv a := by
    apply F.singleObjSection.autEquivSections.injective
    simp only [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    funext d
    apply Aut.ext
    apply Iso.ext
    simp only [GrothendieckSection.autEquivSections_apply]
    rfl
  map_mul' g h := by
    apply F.singleObjSection.autEquivSections.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    funext d
    apply Aut.ext
    apply Iso.ext
    rfl

/-- Recover the original group element from each component of its section label. -/
@[simp]
theorem singleObjSectionAutEquiv_hom_app (g : GrpCat.sectionsSubgroup F) (d : D) :
    (F.singleObjSectionAutEquiv g).asIso.hom.app d = g.val d := by
  simp [singleObjSectionAutEquiv]
  rfl

/-- The inverse identification reads off the fiber arrows. -/
@[simp]
theorem singleObjSectionAutEquiv_symm_apply (a : Aut F.singleObjSection) (d : D) :
    (F.singleObjSectionAutEquiv.symm a).val d = a.asIso.hom.app d := (rfl)

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open Mei.CompletedGroup

variable (F : ℕᵒᵖ ⥤ GrpCat.{w})

/-- A completed group is the automorphism group of the tower's identity-transport section. -/
noncomputable def completedGroupAutEquiv : completedGroup F ≃* Aut F.singleObjSection := by
  let reindex : completedGroup F ≃* GrpCat.sectionsSubgroup F :=
    { toFun := fun g => ⟨fun d => g.val d.unop, fun {l k} f =>
        (mem_completedGroup_iff F g.val).mp g.property k.unop l.unop (leOfHom f.unop)⟩
      invFun := fun g => ⟨fun k => g.val (op k), (mem_completedGroup_iff F _).mpr
        (fun _ _ h => g.property (homOfLE h).op)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact reindex.trans F.singleObjSectionAutEquiv

/-- Each fiber arrow is the corresponding finite-order projection. -/
@[simp]
theorem completedGroupAutEquiv_hom_app (g : completedGroup F) (k : ℕ) :
    (completedGroupAutEquiv F g).asIso.hom.app (op k) = projection k g := by
  simp [completedGroupAutEquiv, projection_apply]
  rfl

/-- Recovering a completed group element from a label retains every finite projection. -/
@[simp]
theorem projection_completedGroupAutEquiv_symm (a : Aut F.singleObjSection) (k : ℕ) :
    projection k ((completedGroupAutEquiv F).symm a) = a.asIso.hom.app (op k) := by
  simp [completedGroupAutEquiv, projection_apply]
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})
  {V : Type*} [Category V] (X : D ⥤ V)
  (ρ : ∀ d, F.obj d →* Aut (X.obj d))
  (hρ : ∀ {d e : D} (f : d ⟶ e) (g : F.obj d),
    (ρ d g).asIso.hom ≫ X.map f = X.map f ≫ (ρ e (F.map f g)).asIso.hom)

/-- The group element carried by the fiber of a total arrow. -/
def singleObjFiber
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a ⟶ b) : F.obj b.base := f.fiber

/-- Constructing a total arrow with a specified group element recovers that element. -/
@[simp]
theorem singleObjFiber_mk
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a.base ⟶ b.base) (g : F.obj b.base) :
    F.singleObjFiber (⟨f, g⟩ : a ⟶ b) = g := (rfl)

/-- The identity total arrow carries the identity group element. -/
@[simp]
theorem singleObjFiber_id
    (a : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)) :
    F.singleObjFiber (𝟙 a) = 1 := by
  simp [singleObjFiber, Grothendieck.id_fiber, MonCat.toCat,
    SingleObj.id_as_one (F.obj a.base)]

/-- Fiber inclusion retains its group element. -/
@[simp]
theorem singleObjFiber_ι_map (d : D) (g : F.obj d) :
    F.singleObjFiber ((Grothendieck.ι (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) d).map
      (X := SingleObj.star (F.obj d)) (Y := SingleObj.star (F.obj d)) g) = g := by
  simp [singleObjFiber, Grothendieck.ι, SingleObj.comp_as_mul (F.obj d),
    SingleObj.id_as_one (F.obj d)]

/-- Composition transports the first group element and then multiplies on the left. -/
@[simp]
theorem singleObjFiber_comp
    {a b c : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a ⟶ b) (g : b ⟶ c) :
    F.singleObjFiber (f ≫ g) = F.singleObjFiber g * (F.map g.base) (F.singleObjFiber f) := by
  simp [singleObjFiber, Grothendieck.comp_fiber, MonCat.toCat,
    SingleObj.comp_as_mul (F.obj c.base), SingleObj.mapHom,
    SingleObj.id_as_one (F.obj c.base), @mul_one (F.obj c.base) _]
  rfl

/-- Compatible actions on a coefficient diagram give a representation of the total
one-object label system. A total arrow first restricts coefficients, then acts.
The abbreviation retains the coefficient objects in dependent morphism types. -/
abbrev singleObjRepresentation :
    Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) ⥤ V where
  obj a := X.obj a.base
  map {a b} f := X.map f.base ≫ (ρ b.base (F.singleObjFiber f)).asIso.hom
  map_id a := by
    simp [singleObjFiber, Grothendieck.id_fiber, MonCat.toCat,
      SingleObj.id_as_one (F.obj a.base)]
  map_comp {a b c} f g := by
    simp only [singleObjFiber_comp, map_mul, Aut.mul_asIso, Iso.trans_hom,
      Grothendieck.comp_base, X.map_comp, Category.assoc]
    rw [← Category.assoc ((ρ b.base) (F.singleObjFiber f)).asIso.hom,
      hρ g.base (F.singleObjFiber f), Category.assoc]

/-- The represented coefficient object over `d` is the original one. -/
@[simp]
theorem singleObjRepresentation_obj
    (a : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)) :
    (F.singleObjRepresentation X ρ hρ).obj a = X.obj a.base := (rfl)

/-- A represented total arrow is restriction followed by its target group action. -/
@[simp]
theorem singleObjRepresentation_map
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)} (f : a ⟶ b) :
    (F.singleObjRepresentation X ρ hρ).map f =
      X.map f.base ≫ (ρ b.base (F.singleObjFiber f)).asIso.hom := (rfl)

/-- The representation acts on a vertical label by the specified group action. -/
theorem singleObjRepresentation_map_ι (d : D) (g : F.obj d) :
    (F.singleObjRepresentation X ρ hρ).map
      ((Grothendieck.ι (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) d).map
        (X := SingleObj.star (F.obj d)) (Y := SingleObj.star (F.obj d)) g) =
      (ρ d g).asIso.hom := by
  rw [singleObjRepresentation_map, singleObjFiber_ι_map]
  simp [Grothendieck.ι]
  rfl

/-- Restriction of the representation to identity transport recovers the coefficient diagram. -/
def singleObjRepresentationIso :
    F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro d e f; simp [singleObjFiber])

/-- The coefficient comparison is the identity at every object. -/
@[simp]
theorem singleObjRepresentationIso_hom_app (d : D) :
    (F.singleObjRepresentationIso X ρ hρ).hom.app d = 𝟙 (X.obj d) := (rfl)

/-- The inverse coefficient comparison is also the identity at every object. -/
@[simp]
theorem singleObjRepresentationIso_inv_app (d : D) :
    (F.singleObjRepresentationIso X ρ hρ).inv.app d = 𝟙 (X.obj d) := (rfl)

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})
  {V : Type*} [Category V] (X : D ⥤ V)
  (ρ : ∀ d, F.obj d →* Aut (X.obj d))
  (hρ : ∀ {d e : D} (f : d ⟶ e) (g : F.obj d),
    (ρ d g).asIso.hom ≫ X.map f = X.map f ≫ (ρ e (F.map f g)).asIso.hom)
  [HasLimit X]

/-- The coefficient limit along identity transport exists whenever the original limit does. -/
instance singleObjRepresentation_hasLimit :
    HasLimit (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) :=
  hasLimit_of_iso (F.singleObjRepresentationIso X ρ hρ).symm

/-- The section-label action, transported to the original coefficient limit. -/
noncomputable def singleObjLimitAction : GrpCat.sectionsSubgroup F →* Aut (limit X) :=
  (Aut.autMulEquivOfIso
    (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ))).toMonoidHom.comp
    ((GrothendieckSection.completedAut (F.singleObjRepresentation X ρ hρ)
      F.singleObjSection).comp F.singleObjSectionAutEquiv.toMonoidHom)

/-- The represented section action recovers the original action at every projection. -/
@[reassoc (attr := simp)]
theorem singleObjLimitAction_hom_π (g : GrpCat.sectionsSubgroup F) (d : D) :
    (F.singleObjLimitAction X ρ hρ g).asIso.hom ≫ limit.π X d =
      limit.π X d ≫ (ρ d (g.val d)).asIso.hom := by
  let e := HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ)
  -- Express conjugation in the underlying category; the automorphism wrappers hide it.
  change (e.inv ≫ (GrothendieckSection.completedAut
    (F.singleObjRepresentation X ρ hρ) F.singleObjSection
      (F.singleObjSectionAutEquiv g)).asIso.hom ≫ e.hom) ≫ limit.π X d = _
  dsimp only [e]
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π,
    singleObjRepresentationIso_hom_app]
  rw [GrothendieckSection.completedAut_hom_π_assoc]
  simp only [singleObjSectionAutEquiv_hom_app]
  simp only [singleObjFiber, Grothendieck.ι, Functor.map_id,
    SingleObj.comp_as_mul (F.obj d)]
  simp only [Category.id_comp, Category.comp_id]
  erw [HasLimit.isoOfNatIso_inv_π_assoc]
  simp [singleObjRepresentationIso, MonCat.toCat, SingleObj.id_as_one (F.obj d)]
  rfl

/-- A levelwise action on the coefficient limit agrees with the represented section action. -/
theorem singleObjLimitAction_unique (σ : GrpCat.sectionsSubgroup F →* Aut (limit X))
    (hσ : ∀ g d, (σ g).asIso.hom ≫ limit.π X d =
      limit.π X d ≫ (ρ d (g.val d)).asIso.hom) :
    σ = F.singleObjLimitAction X ρ hρ := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [hσ, singleObjLimitAction_hom_π]

end CategoryTheory.Functor
