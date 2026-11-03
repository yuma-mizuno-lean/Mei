/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.CategoryTheory.Grothendieck.SingleObj
public import Mei.Geometry.ScatteringDiagram.Groupoid

/-!
# Represented transport along truncation towers

Let `L : J ⥤ Cat` be a diagram of groupoids, for instance the one-object groupoids of the
truncations of a group tower, and let `A : Grothendieck L ⥤ W` be a represented action on
coefficients. A groupoid-labelled wall diagram with values in the groupoid
`GrothendieckSection L` of sections and completed labels assigns to every chamber a section,
and to every wall a completed label between the sections of its two sides. Its transport along an
admissible path is therefore a completed label, which acts by an isomorphism between the
completed coefficient objects `lim_J (s ⋙ A)` of the sections at the two endpoints.

`GroupoidWallDiagram.representedTransport` is this isomorphism. It is the identity along constant
paths, composes along concatenations, is inverted by reversal and is unchanged by subdivision.
Its projection to each level `j` is the coefficient map of the `j`-component of the transport
(`GroupoidWallDiagram.representedTransport_hom_π`), which is the transport of the diagram
obtained by evaluating all sections and labels at `j`
(`GroupoidWallDiagram.map_evaluation_transport`). These fiber transports are compatible with the
transition functors of `L` (`GroupoidWallDiagram.map_evaluation_transport_naturality`), so the
represented transport commutes with truncation. When the coefficient action is faithful on each
fiber and the completed object surjects onto each level, a transport is determined by its
represented transport (`GroupoidWallDiagram.transport_eq_of_representedTransport_eq`).

For a group `H` acting on a section `s` by completed labels, `FiniteWallDiagram.toSectionDiagram`
relabels a group-labelled diagram. Its represented transport along a path is the completed action
of the path product (`FiniteWallDiagram.representedTransport_toSectionDiagram`). For the
identity-transport section of a tower of groups, with the path product an element of the
completed group, this is the levelwise action on the limit of a coefficient diagram
(`FiniteWallDiagram.singleObjLimitAction_pathProduct`).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Mei.Convex Mei.Convex.WallComplement
  Mei.FinitePolyhedralComplex

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace GroupoidWallDiagram

variable {C : FinitePolyhedralComplex h} {J : Type*} [Category J] {L : J ⥤ Cat}
  [∀ j, IsGroupoid (L.obj j)] {W : Type*} [Category W] (A : Grothendieck L ⥤ W)
  (D : GroupoidWallDiagram C (GrothendieckSection L))
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- Transport along an admissible path acts, as a completed label, between the completed
coefficient objects of the sections attached to the endpoint chambers. -/
def representedTransport (p : AdmissiblePLPath x y)
    [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)] [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)] :
    limit ((D.obj (chamber x)).toFunctor ⋙ A) ≅ limit ((D.obj (chamber y)).toFunctor ⋙ A) :=
  GrothendieckSection.completedLabelIso A (D.transport p)

section Projection

variable [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)]
  [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)]

/-- At each `j : J` the represented transport is the coefficient map of the `j`-component of
the transport. -/
@[reassoc (attr := simp)]
theorem representedTransport_hom_π (p : AdmissiblePLPath x y) (j : J) :
    (D.representedTransport A p).hom ≫ limit.π ((D.obj (chamber y)).toFunctor ⋙ A) j =
      limit.π ((D.obj (chamber x)).toFunctor ⋙ A) j ≫
        A.map ((Grothendieck.ι L j).map ((D.transport p).app j)) :=
  GrothendieckSection.completedLabelIso_hom_π A (D.transport p) j

end Projection

/-- The represented transport along a constant path is the identity. -/
@[simp]
theorem representedTransport_nil [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)] :
    D.representedTransport A (Quiver.Path.nil : AdmissiblePLPath x x) = Iso.refl _ := by
  simp [representedTransport]

/-- The represented transport along a concatenation is the composite of the represented
transports, the first path acting first. -/
@[simp]
theorem representedTransport_comp [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)]
    [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)] [HasLimit ((D.obj (chamber z)).toFunctor ⋙ A)]
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.representedTransport A (p.comp q) =
      D.representedTransport A p ≪≫ D.representedTransport A q := by
  simp [representedTransport]

/-- The represented transport along the reversed path is the inverse isomorphism. -/
@[simp]
theorem representedTransport_reverse [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)]
    [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)] (p : AdmissiblePLPath x y) :
    D.representedTransport A p.reverse = (D.representedTransport A p).symm := by
  simp [representedTransport]

/-- Subdividing a path by allowed interior vertices preserves its represented transport. -/
theorem representedTransport_eq_of_isSubdivision [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)]
    [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)] {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) :
    D.representedTransport A q = D.representedTransport A p := by
  simp only [representedTransport, D.transport_eq_of_isSubdivision hpq]

/-- Evaluating the sections and labels of a diagram at `j : J` gives a groupoid-labelled
diagram in the fiber `L j`, whose transport is the `j`-component of the transport. -/
theorem map_evaluation_transport (j : J) (p : AdmissiblePLPath x y) :
    letI : Groupoid (L.obj j) := Groupoid.ofIsGroupoid
    (D.map (GrothendieckSection.evaluation j)).transport p = (D.transport p).app j := by
  let : Groupoid (L.obj j) := Groupoid.ofIsGroupoid
  exact D.transport_map (GrothendieckSection.evaluation j) p

/-- The fiber transports are compatible with the transition functors of the diagram of
groupoids: the transition functor applied to the transport at `j`, followed by the transport
arrow of the target section, is the transport at `k` preceded by that of the source section. -/
theorem map_evaluation_transport_naturality {j k : J} (f : j ⟶ k) (p : AdmissiblePLPath x y) :
    letI : Groupoid (L.obj j) := Groupoid.ofIsGroupoid
    letI : Groupoid (L.obj k) := Groupoid.ofIsGroupoid
    ((D.map (GrothendieckSection.evaluation j)).map (L.map f).toFunctor).transport p ≫
        (D.obj (chamber y)).map f =
      (D.obj (chamber x)).map f ≫ (D.map (GrothendieckSection.evaluation k)).transport p := by
  let : Groupoid (L.obj j) := Groupoid.ofIsGroupoid
  let : Groupoid (L.obj k) := Groupoid.ofIsGroupoid
  rw [GroupoidWallDiagram.transport_map, map_evaluation_transport, map_evaluation_transport]
  exact (D.transport p).naturality f

/-- If the coefficient action is faithful on each fiber and the completed coefficient object
projects epimorphically onto each level, two paths with equal represented transports have equal
transports: the transport is determined by its action. -/
theorem transport_eq_of_representedTransport_eq [∀ j, (Grothendieck.ι L j ⋙ A).Faithful]
    [HasLimit ((D.obj (chamber x)).toFunctor ⋙ A)] [HasLimit ((D.obj (chamber y)).toFunctor ⋙ A)]
    [∀ j, Epi (limit.π ((D.obj (chamber x)).toFunctor ⋙ A) j)] {p q : AdmissiblePLPath x y}
    (hpq : D.representedTransport A p = D.representedTransport A q) :
    D.transport p = D.transport q := by
  refine GrothendieckSection.Hom.ext (funext fun j => ?_)
  apply (Grothendieck.ι L j ⋙ A).map_injective
  refine (cancel_epi (limit.π ((D.obj (chamber x)).toFunctor ⋙ A) j)).mp ?_
  have := congrArg (fun e => e.hom ≫ limit.π ((D.obj (chamber y)).toFunctor ⋙ A) j) hpq
  simp only [representedTransport_hom_π] at this
  exact this

end GroupoidWallDiagram

namespace FiniteWallDiagram

variable {C : FinitePolyhedralComplex h} {J : Type*} [Category J] {L : J ⥤ Cat}
  [∀ j, IsGroupoid (L.obj j)] {W : Type*} [Category W] (A : Grothendieck L ⥤ W)
  {H : Type*} [Group H] (D : FiniteWallDiagram C H) (s : GrothendieckSection L) (φ : H →* Aut s)
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- A group acting on a section by completed labels sends a group-labelled diagram to a diagram
labelled by completed labels on the constant section. -/
@[expose, reducible]
def toSectionDiagram : GroupoidWallDiagram C (GrothendieckSection L) :=
  D.toGroupoidWallDiagram.map (SingleObj.functor (Aut.toEnd.comp φ))

/-- The label of a wall of the relabelled diagram is the completed label of the original label. -/
theorem toSectionDiagram_label (P : C.walls) :
    (D.toSectionDiagram s φ).label P = (φ (D.label P)).asIso.hom := (rfl)

/-- The coefficient limit at every chamber of the relabelled diagram is that of the section. -/
instance hasLimit_toSectionDiagram_obj [HasLimit (s.toFunctor ⋙ A)]
    (c : Chamber (fun P : C.walls => (P : Set V))) :
    HasLimit (((D.toSectionDiagram s φ).obj c).toFunctor ⋙ A) :=
  inferInstanceAs (HasLimit (s.toFunctor ⋙ A))

/-- The transport of the relabelled diagram is the completed label of the path product. -/
theorem transport_toSectionDiagram (p : AdmissiblePLPath x y) :
    (D.toSectionDiagram s φ).transport p = (φ (D.pathProduct p)).asIso.hom := by
  simp [toSectionDiagram]

/-- The represented transport of the relabelled diagram is the completed action of the path
product. -/
theorem representedTransport_toSectionDiagram [HasLimit (s.toFunctor ⋙ A)]
    (p : AdmissiblePLPath x y) :
    (D.toSectionDiagram s φ).representedTransport A p =
      (GrothendieckSection.completedAut A s (φ (D.pathProduct p))).asIso := by
  apply Iso.ext
  apply limit.hom_ext
  intro j
  -- The relabelled chamber objects are the section `s` only up to reducible unfolding.
  erw [GroupoidWallDiagram.representedTransport_hom_π, transport_toSectionDiagram]
  exact (GrothendieckSection.completedAut_hom_π A s (φ (D.pathProduct p)) j).symm

section Tower

variable {C : FinitePolyhedralComplex h} {J : Type*} [Category J] (F : J ⥤ GrpCat)
  {W : Type*} [Category W] (X : J ⥤ W) (ρ : ∀ j, F.obj j →* Aut (X.obj j))
  (hρ : ∀ {j k : J} (f : j ⟶ k) (g : F.obj j),
    (ρ j g).asIso.hom ≫ X.map f = X.map f ≫ (ρ k (F.map f g)).asIso.hom)
  [HasLimit X] (D : FiniteWallDiagram C (GrpCat.sectionsSubgroup F))
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- For a diagram labelled by the compatible families of a tower of groups, the represented
transport on the identity-transport section is the levelwise action of the path product on the
limit of the coefficient diagram, up to the identification of the limit with that of the
represented diagram. -/
theorem singleObjLimitAction_pathProduct (p : AdmissiblePLPath x y) :
    F.singleObjLimitAction X ρ hρ (D.pathProduct p) =
      Aut.autMulEquivOfIso (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ))
        (Aut.of ((D.toSectionDiagram F.singleObjSection
          F.singleObjSectionAutEquiv.toMonoidHom).representedTransport
            (F.singleObjRepresentation X ρ hρ) p)) := by
  rw [representedTransport_toSectionDiagram]
  apply Aut.ext
  apply Iso.ext
  apply limit.hom_ext
  intro j
  have hom_π : (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ)).hom ≫
      limit.π X j =
        limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) j := by
    rw [HasLimit.isoOfNatIso_hom_π, F.singleObjRepresentationIso_hom_app]
    exact Category.comp_id _
  have inv_π : (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ)).inv ≫
      limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) j =
        limit.π X j := by
    rw [HasLimit.isoOfNatIso_inv_π, F.singleObjRepresentationIso_inv_app]
    exact Category.comp_id _
  rw [F.singleObjLimitAction_hom_π]
  simp only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hom_π, GrothendieckSection.completedAut_hom_π]
  erw [← Category.assoc, inv_π]
  -- The section object is the unique object, so the vertical-action formula applies.
  exact congrArg _ ((F.singleObjRepresentation_map_ι X ρ hρ j _).symm.trans
    (congrArg _ (by erw [F.singleObjSectionAutEquiv_hom_app])))

end Tower

end FiniteWallDiagram

end Mei
