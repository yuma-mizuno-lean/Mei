/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Coarsening
public import Mei.Geometry.ScatteringDiagram.Groupoid

/-!
# Compatible refinements of groupoid-labelled wall diagrams

A compatible refinement of a groupoid-labelled wall diagram `D` lives on a subdivision of its
complex. Its chambers are finer than those of `D`, so it comes with identifications of the
object of each new chamber with the object of the chamber of `D` containing it. A new wall
contained in a wall of `D` has a positively proportional coorientation and its arrow is
the arrow of that wall, transported along the identifications; every other new wall has its
two sides in one chamber of `D` and carries the identity.

Such a refinement has the same transport as `D` along every polygonal path admissible for
both wall families, up to the identifications of the objects at the endpoints. The
comparison follows the crossing letters of the path, coarsened by
`Quiver.Path.crossingLetters_coarsen` (`CompatibleRefinement.transport_comp_objIso`). Every
diagram `D` has such a refinement on every subdivision of its complex with prescribed
coorientations (`GroupoidWallDiagram.refinement`).

The group-labelled case is `Mei.FiniteWallDiagram.IsCompatibleRefinement`; the sign and
ordering conventions are those of Bridgeland, *Scattering diagrams, Hall algebras and
stability conditions*, §2, [arXiv:1603.00416](https://arxiv.org/abs/1603.00416).
-/

public section

noncomputable section

open CategoryTheory Mei.Convex Mei.Convex.WallComplement Mei.FinitePolyhedralComplex

namespace Mei.GroupoidWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C C' : FinitePolyhedralComplex h} {G : Type*} [Groupoid G]

/-- `E` is a compatible refinement of `D`: the complex of `E` subdivides that of `D`, the
object of each chamber of `E` is identified with the object of the chamber of `D` containing
it, a wall inside a wall of `D` has a positively proportional coorientation and the arrow of
that wall, and every other wall carries the identity. -/
structure CompatibleRefinement (E : GroupoidWallDiagram C' G) (D : GroupoidWallDiagram C G) where
  /-- The complex of `E` subdivides the complex of `D`. -/
  isSubdivision : C'.IsSubdivision C
  /-- The object of a chamber of `E` is identified with that of the chamber of `D`
  containing it. -/
  objIso : ∀ c, E.obj c ≅ D.obj (isSubdivision.restrictChamber c)
  /-- A wall inside a wall of `D` has a positively proportional coorientation. -/
  exists_pos_normal_eq_smul : ∀ (Q : C'.walls) (P : C.walls), (Q : Set V) ⊆ P →
    ∃ c : ℝ, 0 < c ∧ E.normal Q = c • D.normal P
  /-- A wall inside a wall of `D` carries the arrow of that wall, up to the identifications
  of its two sides. -/
  label_comp_objIso_of_subset : ∀ (Q : C'.walls) (P : C.walls) (hQP : (Q : Set V) ⊆ P),
    E.label Q ≫ (objIso (C'.negativeChamber Q (E.normal Q) (E.ker_normal Q))).hom =
      (objIso (C'.positiveChamber Q (E.normal Q) (E.ker_normal Q))).hom ≫
        eqToHom (congrArg D.obj (isSubdivision.restrictChamber_positiveChamber hQP
          (E.ker_normal Q) (D.ker_normal P) (exists_pos_normal_eq_smul Q P hQP))) ≫
        D.label P ≫
        eqToHom (congrArg D.obj (isSubdivision.restrictChamber_negativeChamber hQP
          (E.ker_normal Q) (D.ker_normal P) (exists_pos_normal_eq_smul Q P hQP)).symm)
  /-- A wall inside no wall of `D` carries the identity, up to the identifications of its
  two sides. -/
  label_comp_objIso_of_forall_not_subset : ∀ (Q : C'.walls)
    (hQ : ∀ P : C.walls, ¬(Q : Set V) ⊆ P),
    E.label Q ≫ (objIso (C'.negativeChamber Q (E.normal Q) (E.ker_normal Q))).hom =
      (objIso (C'.positiveChamber Q (E.normal Q) (E.ker_normal Q))).hom ≫
        eqToHom (congrArg D.obj
          (isSubdivision.restrictChamber_positiveChamber_eq_negativeChamber hQ (E.ker_normal Q)))

namespace CompatibleRefinement

variable {E : GroupoidWallDiagram C' G} {D : GroupoidWallDiagram C G}
  (R : CompatibleRefinement E D)

/-- A crossing of a wall inside a wall `P` of `D` is, up to the identifications of the
objects, the crossing of `P` with the same sign. -/
theorem letterHom_comp_objIso_of_subset {l : C'.walls × Bool} {P : C.walls}
    (hlP : (l.1 : Set V) ⊆ P) :
    E.letterHom l ≫ (R.objIso (C'.crossingTarget E.normal E.ker_normal l)).hom =
      (R.objIso (C'.crossingSource E.normal E.ker_normal l)).hom ≫
        eqToHom (congrArg D.obj (R.isSubdivision.restrictChamber_crossingSource E.ker_normal
          D.ker_normal hlP (R.exists_pos_normal_eq_smul l.1 P hlP))) ≫
        D.letterHom (P, l.2) ≫
        eqToHom (congrArg D.obj (R.isSubdivision.restrictChamber_crossingTarget E.ker_normal
          D.ker_normal hlP (R.exists_pos_normal_eq_smul l.1 P hlP)).symm) := by
  obtain ⟨Q, _ | _⟩ := l
  · simpa only [letterHom_false] using R.label_comp_objIso_of_subset Q P hlP
  · have key := R.label_comp_objIso_of_subset Q P hlP
    simp only [letterHom_true]
    rw [IsIso.inv_comp_eq, ← Category.assoc, key]
    simp

/-- A crossing of a wall inside no wall of `D` is, up to the identifications of the objects,
the identity. -/
theorem letterHom_comp_objIso_of_forall_not_subset {l : C'.walls × Bool}
    (hl : ∀ P : C.walls, ¬(l.1 : Set V) ⊆ P) :
    E.letterHom l ≫ (R.objIso (C'.crossingTarget E.normal E.ker_normal l)).hom =
      (R.objIso (C'.crossingSource E.normal E.ker_normal l)).hom ≫
        eqToHom (congrArg D.obj
          (R.isSubdivision.restrictChamber_crossingSource_eq_crossingTarget E.ker_normal hl)) := by
  obtain ⟨Q, _ | _⟩ := l
  · simpa only [letterHom_false] using R.label_comp_objIso_of_forall_not_subset Q hl
  · have key := R.label_comp_objIso_of_forall_not_subset Q hl
    simp only [letterHom_true]
    rw [IsIso.inv_comp_eq, ← Category.assoc, key]
    simp

/-- A chain of crossings of `E` composes, up to the identifications of the objects, to the
composite of the coarsened chain of crossings of `D`. -/
theorem chainHom_comp_objIso {L : List (C'.walls × Bool)}
    {a b : Chamber (fun P : C'.walls => (P : Set V))}
    (hL : C'.IsCrossingChain E.normal E.ker_normal a b L)
    {a' b' : Chamber (fun P : C.walls => (P : Set V))}
    (ha : R.isSubdivision.restrictChamber a = a') (hb : R.isSubdivision.restrictChamber b = b')
    (hL' : C.IsCrossingChain D.normal D.ker_normal a' b' (L.filterMap (coarsenLetter C))) :
    E.chainHom L hL ≫ (R.objIso b).hom ≫ eqToHom (congrArg D.obj hb) =
      (R.objIso a).hom ≫ eqToHom (congrArg D.obj ha) ≫
        D.chainHom (L.filterMap (coarsenLetter C)) hL' := by
  induction L generalizing a a' with
  | nil =>
    obtain rfl := isCrossingChain_nil.mp hL
    obtain rfl := ha
    obtain rfl := hb
    simp
  | cons l L ih =>
    obtain ⟨rfl, hL₂⟩ := (isCrossingChain_cons l L).mp hL
    rw [chainHom_cons]
    simp only [eqToHom_refl, Category.id_comp, Category.assoc]
    cases hcl : coarsenLetter C l with
    | none =>
      have hl := coarsenLetter_eq_none.mp hcl
      have hL'' : C.IsCrossingChain D.normal D.ker_normal a' b'
          (L.filterMap (coarsenLetter C)) := by
        simpa only [List.filterMap_cons_none hcl] using hL'
      rw [D.chainHom_congr hL' hL'' (List.filterMap_cons_none hcl)]
      have ih' := ih hL₂ ((R.isSubdivision.restrictChamber_crossingSource_eq_crossingTarget
        E.ker_normal hl).symm.trans ha) hL''
      rw [ih', ← Category.assoc, R.letterHom_comp_objIso_of_forall_not_subset hl,
        Category.assoc, eqToHom_trans_assoc]
    | some m =>
      obtain ⟨P, s⟩ := m
      obtain ⟨hlP, rfl⟩ := coarsenLetter_eq_some.mp hcl
      have hcons := List.filterMap_cons_some (f := coarsenLetter C) (a := l) (l := L) hcl
      have hL'₂ : C.IsCrossingChain D.normal D.ker_normal a' b'
          ((P, l.2) :: L.filterMap (coarsenLetter C)) := hcons ▸ hL'
      obtain ⟨rfl, hL''⟩ := (isCrossingChain_cons _ _).mp hL'₂
      rw [D.chainHom_congr hL' hL'₂ hcons, D.chainHom_cons]
      have ih' := ih hL₂ (R.isSubdivision.restrictChamber_crossingTarget E.ker_normal
        D.ker_normal hlP (R.exists_pos_normal_eq_smul l.1 P hlP)) hL''
      simp only [eqToHom_refl, Category.id_comp]
      rw [ih', ← Category.assoc, R.letterHom_comp_objIso_of_subset hlP]
      simp

/-- A compatible refinement has the same transport as the diagram it refines along every
polygonal path admissible for both wall families, up to the identifications of the objects
at the endpoints. -/
theorem transport_comp_objIso {x y : WallComplement (fun P : C'.walls => (P : Set V))}
    {x' y' : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    E.transport p ≫ (R.objIso (chamber y)).hom ≫
        eqToHom (congrArg D.obj (R.isSubdivision.restrictChamber_chamber
          (Quiver.Path.endpoints_val_eq_of_vertices_eq p q hpq).2)) =
      (R.objIso (chamber x)).hom ≫
        eqToHom (congrArg D.obj (R.isSubdivision.restrictChamber_chamber
          (Quiver.Path.endpoints_val_eq_of_vertices_eq p q hpq).1)) ≫ D.transport q := by
  obtain ⟨hx, hy⟩ := Quiver.Path.endpoints_val_eq_of_vertices_eq p q hpq
  have hq := Quiver.Path.crossingLetters_coarsen R.isSubdivision E.normal D.normal
    R.exists_pos_normal_eq_smul p q hpq
  have hL' : C.IsCrossingChain D.normal D.ker_normal (chamber x') (chamber y')
      ((p.crossingLetters E.normal).filterMap (coarsenLetter C)) :=
    hq ▸ q.isCrossingChain_crossingLetters D.normal D.ker_normal
  rw [transport_def, transport_def, D.chainHom_congr _ hL' hq]
  exact R.chainHom_comp_objIso (p.isCrossingChain_crossingLetters E.normal E.ker_normal)
    (R.isSubdivision.restrictChamber_chamber hx) (R.isSubdivision.restrictChamber_chamber hy) hL'

end CompatibleRefinement

variable (D : GroupoidWallDiagram C G) (hCD : C'.IsSubdivision C) (ν : C'.walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ Q, LinearMap.ker (ν Q) = (affineSpan ℝ (Q : Set V)).direction)
  (hνD : ∀ (Q : C'.walls) (P : C.walls), (Q : Set V) ⊆ P → ∃ c : ℝ, 0 < c ∧ ν Q = c • D.normal P)

open scoped Classical in
/-- The compatible refinement of `D` on a subdivision: each chamber has the object of the
chamber of `D` containing it, a wall inside a wall `P` of `D` the arrow of `P`, and every
other wall the identity. -/
-- Reducible and exposed, so that the objects of the chambers compute to those of `D`.
@[expose, reducible]
def refinement : GroupoidWallDiagram C' G where
  normal := ν
  ker_normal := hν
  obj c := D.obj (hCD.restrictChamber c)
  label Q :=
    if hQ : ∃ P : C.walls, (Q : Set V) ⊆ P then
      eqToHom (congrArg D.obj (hCD.restrictChamber_positiveChamber hQ.choose_spec (hν Q)
        (D.ker_normal hQ.choose) (hνD Q hQ.choose hQ.choose_spec))) ≫ D.label hQ.choose ≫
      eqToHom (congrArg D.obj (hCD.restrictChamber_negativeChamber hQ.choose_spec (hν Q)
        (D.ker_normal hQ.choose) (hνD Q hQ.choose hQ.choose_spec)).symm)
    else
      eqToHom (congrArg D.obj (hCD.restrictChamber_positiveChamber_eq_negativeChamber
        (not_exists.mp hQ) (hν Q)))

/-- The arrow of a wall inside a wall `P` of `D` is the arrow of `P`, up to the
identifications of the objects. -/
theorem refinement_label_of_subset {Q : C'.walls} {P : C.walls} (hQP : (Q : Set V) ⊆ P) :
    (D.refinement hCD ν hν hνD).label Q =
      eqToHom (congrArg D.obj (hCD.restrictChamber_positiveChamber hQP (hν Q)
        (D.ker_normal P) (hνD Q P hQP))) ≫ D.label P ≫
      eqToHom (congrArg D.obj (hCD.restrictChamber_negativeChamber hQP (hν Q)
        (D.ker_normal P) (hνD Q P hQP)).symm) := by
  classical
  have hQ : ∃ P : C.walls, (Q : Set V) ⊆ P := ⟨P, hQP⟩
  have hc : hQ.choose = P := Subtype.ext (eq_of_subset_of_mem_walls Q.property
    hQ.choose.property P.property hQ.choose_spec hQP)
  simp only [refinement, dite_eq_left hQ]
  -- After identifying the chosen wall with `P`, both sides differ only in their proofs.
  subst hc
  rfl

/-- The arrow of a wall inside no wall of `D` is the identity, up to the identifications of
the objects. -/
theorem refinement_label_of_forall_not_subset {Q : C'.walls}
    (hQ : ∀ P : C.walls, ¬(Q : Set V) ⊆ P) :
    (D.refinement hCD ν hν hνD).label Q =
      eqToHom (congrArg D.obj
        (hCD.restrictChamber_positiveChamber_eq_negativeChamber hQ (hν Q))) := by
  classical
  simp only [refinement, dite_eq_right (not_exists.mpr hQ)]

/-- The refinement of `D` on a subdivision is a compatible refinement of `D`. -/
def CompatibleRefinement.refinement :
    CompatibleRefinement (D.refinement hCD ν hν hνD) D where
  isSubdivision := hCD
  objIso _ := Iso.refl _
  exists_pos_normal_eq_smul := hνD
  label_comp_objIso_of_subset Q P hQP := by
    rw [D.refinement_label_of_subset hCD ν hν hνD hQP]
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  label_comp_objIso_of_forall_not_subset Q hQ := by
    rw [D.refinement_label_of_forall_not_subset hCD ν hν hνD hQ]
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end Mei.GroupoidWallDiagram
