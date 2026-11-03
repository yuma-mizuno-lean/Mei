/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.AffineTransport
public import Mei.Geometry.ScatteringDiagram.Groupoid

/-!
# Affine transport of groupoid-labelled wall diagrams

An integral affine equivalence `e` carries a groupoid-labelled wall diagram `D` on a complex
`C` to a diagram `D.image e` on the image complex `C.image e`. The chambers of the image
complement are identified with those of `C` (`FinitePolyhedralComplex.chamberEquiv`), so the
image diagram has the objects of `D` on the identified chambers, coorientations pulled back
along the inverse linear part, and the arrows of `D` on the image walls.

Transport along an admissible path of `C` and along its image path agree up to the equalities
identifying the objects of the endpoint chambers (`transport_image`). For a group, viewed as a
one-object groupoid, the identifications are trivial and transport along the image path is the
path product of the original diagram
(`Mei.FiniteWallDiagram.transport_image_toGroupoidWallDiagram`), as for the affine image of
group-labelled diagrams (`Mei.FiniteWallDiagram.pathProduct_image`).
-/

public section

noncomputable section

open CategoryTheory Mei.Convex Mei.Convex.WallComplement Mei.FinitePolyhedralComplex

namespace Mei.GroupoidWallDiagram

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {C : FinitePolyhedralComplex h} {G G' : Type*} [Groupoid G] [Groupoid G']
  (D : GroupoidWallDiagram C G) (e : Mei.Toric.IntegralAffineEquiv h h')

/-- The wall arrow depends on the wall only up to the equality of its side chambers. -/
theorem label_eq_of_eq {P P' : C.walls} (hP : P = P') :
    D.label P = eqToHom (congrArg (fun P => D.obj (C.positiveChamber P (D.normal P)
      (D.ker_normal P))) hP) ≫ D.label P' ≫ eqToHom (congrArg (fun P => D.obj
        (C.negativeChamber P (D.normal P) (D.ker_normal P))) hP.symm) := by
  subst hP
  simp

/-- The affine image of a groupoid-labelled diagram: the objects and arrows of `D`, placed on
the identified chambers and image walls, with coorientations pulled back along the inverse
linear part. -/
-- Reducible and exposed, so that the image objects compute to those of `D` in the types of
-- arrows and equalities of objects.
@[expose, reducible]
def image : GroupoidWallDiagram (C.image e) G where
  normal := C.imageNormal e D.normal
  ker_normal := C.ker_imageNormal e D.normal D.ker_normal
  obj c := D.obj ((C.chamberEquiv e).symm c)
  label Q :=
    eqToHom (congrArg D.obj (C.chamberEquiv_symm_positiveChamber e _ Q
      (Equiv.apply_symm_apply _ _) _ (D.ker_normal _) _ _ (C.imageNormal_comp_symm e _ Q))) ≫
    D.label ((C.wallImageEquiv e).symm Q) ≫
    eqToHom (congrArg D.obj (C.chamberEquiv_symm_negativeChamber e _ Q
      (Equiv.apply_symm_apply _ _) _ (D.ker_normal _) _ _ (C.imageNormal_comp_symm e _ Q))).symm

/-- The image diagram has the coorientations pulled back along the inverse linear part. -/
@[simp]
theorem image_normal : (D.image e).normal = C.imageNormal e D.normal := (rfl)

/-- The image diagram has the objects of `D` on the identified chambers. -/
@[simp]
theorem image_obj (c : Chamber (fun Q : (C.image e).walls => (Q : Set V'))) :
    (D.image e).obj c = D.obj ((C.chamberEquiv e).symm c) := (rfl)

/-- The objects of the image diagram at the identified chambers are those of `D`. -/
theorem image_obj_chamberEquiv (c : Chamber (fun P : C.walls => (P : Set V))) :
    (D.image e).obj (C.chamberEquiv e c) = D.obj c := by
  rw [image_obj, Equiv.symm_apply_apply]

/-- The wall arrow of an image wall, in terms of the arrow of the wall it comes from. -/
theorem image_label_wallImageEquiv (P : C.walls) :
    (D.image e).label (C.wallImageEquiv e P) =
      eqToHom (congrArg D.obj (C.chamberEquiv_symm_positiveChamber e P _ rfl _ (D.ker_normal P) _ _
        (C.imageNormal_comp e _ P))) ≫ D.label P ≫
      eqToHom (congrArg D.obj (C.chamberEquiv_symm_negativeChamber e P _ rfl _ (D.ker_normal P) _ _
        (C.imageNormal_comp e _ P))).symm := by
  dsimp only [image]
  rw [label_eq_of_eq D (Equiv.symm_apply_apply (C.wallImageEquiv e) P)]
  simp only [eqToHom_trans_assoc, eqToHom_trans, Category.assoc]

/-- A crossing letter of the image diagram has the arrow of the original letter, up to the
equalities of its side objects. -/
theorem letterHom_image (l : C.walls × Bool) :
    (D.image e).letterHom (Prod.map (C.wallImageEquiv e) id l) =
      eqToHom (congrArg D.obj (C.chamberEquiv_symm_crossingSource e D.normal D.ker_normal _
        (C.ker_imageNormal e D.normal D.ker_normal) (C.imageNormal_comp e _) l)) ≫
      D.letterHom l ≫
      eqToHom (congrArg D.obj (C.chamberEquiv_symm_crossingTarget e D.normal D.ker_normal _
        (C.ker_imageNormal e D.normal D.ker_normal) (C.imageNormal_comp e _) l)).symm := by
  obtain ⟨P, _ | _⟩ := l
  · simpa using D.image_label_wallImageEquiv e P
  · simp only [Prod.map_apply, id_eq, letterHom_true]
    simp only [IsIso.inv_comp, inv_eqToHom, Category.assoc]
    rw [label_eq_of_eq D (Equiv.symm_apply_apply (C.wallImageEquiv e) P)]
    simp only [IsIso.inv_comp, inv_eqToHom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

variable {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- The composite along a transported chain is the composite along the original chain, up to
the equalities of the endpoint objects. -/
theorem chainHom_image {a b : Chamber (fun P : C.walls => (P : Set V))}
    {a' b' : Chamber (fun Q : (C.image e).walls => (Q : Set V'))}
    (ha : C.chamberEquiv e a = a') (hb : C.chamberEquiv e b = b')
    {L : List (C.walls × Bool)} (hL : C.IsCrossingChain D.normal D.ker_normal a b L)
    (hL' : (C.image e).IsCrossingChain (D.image e).normal (D.image e).ker_normal a' b'
      (L.map (Prod.map (C.wallImageEquiv e) id))) :
    (D.image e).chainHom (L.map (Prod.map (C.wallImageEquiv e) id)) hL' =
      eqToHom ((congrArg (D.image e).obj ha).symm.trans (D.image_obj_chamberEquiv e a)) ≫
        D.chainHom L hL ≫
        eqToHom ((D.image_obj_chamberEquiv e b).symm.trans (congrArg (D.image e).obj hb)) := by
  induction L generalizing a a' with
  | nil =>
    obtain rfl : a = b := isCrossingChain_nil.mp hL
    subst ha hb
    simp
  | cons l L ih =>
    obtain ⟨rfl, hL₁⟩ := (isCrossingChain_cons _ _).mp hL
    subst ha
    simp only [List.map_cons, chainHom_cons, letterHom_image]
    rw [ih (C.chamberEquiv_crossingTarget e D.normal D.ker_normal _
      (C.ker_imageNormal e D.normal D.ker_normal) (C.imageNormal_comp e _) l) hL₁]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The object of the image diagram at the chamber of an image point is the object of `D` at
the chamber of the original point. -/
theorem image_obj_chamber (x : WallComplement (fun P : C.walls => (P : Set V))) :
    (D.image e).obj (chamber ((C.pathImage e).obj x)) = D.obj (chamber x) := by
  rw [← C.chamberEquiv_chamber e x, image_obj_chamberEquiv]

/-- Transport along the image of an admissible path is transport along the path, up to the
equalities of the endpoint objects. -/
theorem transport_image (p : AdmissiblePLPath x y) :
    (D.image e).transport ((C.pathImage e).mapPath p) =
      eqToHom (D.image_obj_chamber e x) ≫ D.transport p ≫
        eqToHom (D.image_obj_chamber e y).symm := by
  have hlet := Quiver.Path.crossingLetters_pathImage p e D.normal (D.image e).normal
    (C.imageNormal_comp e D.normal)
  have hL' := hlet ▸ ((C.pathImage e).mapPath p).isCrossingChain_crossingLetters
    (D.image e).normal (D.image e).ker_normal
  rw [transport_def, (D.image e).chainHom_congr _ hL' hlet, transport_def,
    D.chainHom_image e (C.chamberEquiv_chamber e x) (C.chamberEquiv_chamber e y)
      (p.isCrossingChain_crossingLetters D.normal D.ker_normal) hL']

end Mei.GroupoidWallDiagram

namespace Mei.FiniteWallDiagram

variable {N N' V V' H : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {C : FinitePolyhedralComplex h} [Group H] (D : FiniteWallDiagram C H)
  (e : Mei.Toric.IntegralAffineEquiv h h')
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- For a group-labelled diagram, transport along an image path in the affine image of its
groupoid form is the path product of the original path. -/
@[simp]
theorem transport_image_toGroupoidWallDiagram (p : AdmissiblePLPath x y) :
    ((D.toGroupoidWallDiagram.image e).transport ((C.pathImage e).mapPath p) : H) =
      D.pathProduct p := by
  rw [GroupoidWallDiagram.transport_image]
  simp

end Mei.FiniteWallDiagram
