/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Itinerary
public import Mei.Geometry.ScatteringDiagram.Finite

/-!
# Groupoid-labelled wall diagrams and their transport

A groupoid-labelled wall diagram on a finite polyhedral complex assigns an object of a
groupoid `G` to every chamber of the wall complement, and to every cooriented wall an
arrow from the object of its positive chamber to the object of its negative chamber.
Crossing the wall against its coorientation uses this arrow, crossing along it uses
the inverse. Transport along an admissible path composes these arrows in traversal
order: for successive crossings `ℓ₁, …, ℓₛ` it is `ℓ₁ ≫ ⋯ ≫ ℓₛ`, the composite
`ℓₛ ∘ ⋯ ∘ ℓ₁`. Such labels arise when the coefficient objects themselves vary from
chamber to chamber, for instance in a fiber of a functor to groupoids.

Transport is defined on the crossing letters of the path, which form a chain of
incident chambers (`Quiver.Path.isCrossingChain_crossingLetters`). It is functorial
for concatenation, inverted by reversal, unchanged by path subdivision, and natural
for functors between groupoids. For a group `H`, viewed as the one-object groupoid
`SingleObj H`, every chamber carries the unique object and transport is the path
product of the corresponding group-labelled diagram
(`Mei.FiniteWallDiagram.transport_toGroupoidWallDiagram`). This follows the crossing-word
evaluation of `Mei.FiniteWallDiagram.pathProduct`, with Bridgeland's sign and order
convention for path-ordered products (Bridgeland, *Scattering diagrams, Hall algebras
and stability conditions*, §2, arXiv:1603.00416v4).
-/

public section

noncomputable section

open CategoryTheory Mei.Convex Mei.Convex.WallComplement Mei.FinitePolyhedralComplex

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Objects of a groupoid on the chambers of a finite complex, with an arrow for each
cooriented wall from the object of its positive chamber to that of its negative chamber.
Its inverse is the arrow of the opposite crossing. -/
structure GroupoidWallDiagram (C : FinitePolyhedralComplex h) (G : Type*) [Groupoid G] where
  /-- A linear representative of the coorientation of each wall. -/
  normal : C.walls → V →ₗ[ℝ] ℝ
  /-- The normal cuts out exactly the wall direction. -/
  ker_normal : ∀ P, LinearMap.ker (normal P) = (affineSpan ℝ (P : Set V)).direction
  /-- The object attached to each chamber. -/
  obj : Chamber (fun P : C.walls => (P : Set V)) → G
  /-- The arrow of a crossing against the coorientation of each wall. -/
  label : ∀ P, obj (C.positiveChamber P (normal P) (ker_normal P)) ⟶
    obj (C.negativeChamber P (normal P) (ker_normal P))

namespace GroupoidWallDiagram

variable {C : FinitePolyhedralComplex h} {G G' G'' : Type*} [Groupoid G] [Groupoid G']
  [Groupoid G''] (D : GroupoidWallDiagram C G)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- The arrow of one signed crossing: the inverse label along the coorientation, the
label against it. -/
def letterHom : (l : C.walls × Bool) →
    (D.obj (C.crossingSource D.normal D.ker_normal l) ⟶
      D.obj (C.crossingTarget D.normal D.ker_normal l))
  | (P, true) => Groupoid.inv (D.label P)
  | (P, false) => D.label P

/-- Along the coorientation a crossing uses the inverse label. -/
@[simp]
theorem letterHom_true (P : C.walls) : D.letterHom (P, true) = inv (D.label P) :=
  Groupoid.inv_eq_inv _

/-- Against the coorientation a crossing uses the label. -/
@[simp]
theorem letterHom_false (P : C.walls) : D.letterHom (P, false) = D.label P := (rfl)

/-- The composite of the letter arrows along a chain of crossings, in traversal order. -/
def chainHom : (L : List (C.walls × Bool)) → {a b : Chamber (fun P : C.walls => (P : Set V))} →
    C.IsCrossingChain D.normal D.ker_normal a b L → (D.obj a ⟶ D.obj b)
  | [], _, _, hL => eqToHom (congrArg D.obj (isCrossingChain_nil.mp hL))
  | l :: L, _, _, hL => eqToHom (congrArg D.obj ((isCrossingChain_cons l L).mp hL).1) ≫
      D.letterHom l ≫ chainHom L ((isCrossingChain_cons l L).mp hL).2

variable {a b c : Chamber (fun P : C.walls => (P : Set V))}

/-- The empty chain composes to the equality arrow between its endpoint objects. -/
@[simp]
theorem chainHom_nil (hL : C.IsCrossingChain D.normal D.ker_normal a b []) :
    D.chainHom [] hL = eqToHom (congrArg D.obj (isCrossingChain_nil.mp hL)) := (rfl)

/-- Prepending a crossing composes its arrow with the composite of the remaining chain. -/
@[simp]
theorem chainHom_cons (l : C.walls × Bool) (L : List (C.walls × Bool))
    (hL : C.IsCrossingChain D.normal D.ker_normal a b (l :: L)) :
    D.chainHom (l :: L) hL =
      eqToHom (congrArg D.obj ((isCrossingChain_cons l L).mp hL).1) ≫
        D.letterHom l ≫ D.chainHom L ((isCrossingChain_cons l L).mp hL).2 := (rfl)

/-- The composite along a chain depends only on the list of letters. -/
theorem chainHom_congr {L L' : List (C.walls × Bool)}
    (hL : C.IsCrossingChain D.normal D.ker_normal a b L)
    (hL' : C.IsCrossingChain D.normal D.ker_normal a b L') (he : L = L') :
    D.chainHom L hL = D.chainHom L' hL' := by
  subst he
  rfl

/-- Composites along concatenated chains compose. -/
theorem chainHom_append {L₁ L₂ : List (C.walls × Bool)}
    (h₁ : C.IsCrossingChain D.normal D.ker_normal a c L₁)
    (h₂ : C.IsCrossingChain D.normal D.ker_normal c b L₂)
    (h : C.IsCrossingChain D.normal D.ker_normal a b (L₁ ++ L₂)) :
    D.chainHom (L₁ ++ L₂) h = D.chainHom L₁ h₁ ≫ D.chainHom L₂ h₂ := by
  induction L₁ generalizing a with
  | nil =>
    obtain rfl : a = c := isCrossingChain_nil.mp h₁
    simp [chainHom]
  | cons l L₁ ih =>
    obtain ⟨rfl, h₁'⟩ := (isCrossingChain_cons _ _).mp h₁
    simp only [List.cons_append, chainHom, Category.assoc]
    rw [ih h₁' ((isCrossingChain_cons _ _).mp h).2]

/-- The opposite crossing of a single letter has the inverse arrow. -/
theorem chainHom_singleton_flip (l : C.walls × Bool)
    (hl : C.IsCrossingChain D.normal D.ker_normal (C.crossingTarget D.normal D.ker_normal l)
      (C.crossingSource D.normal D.ker_normal l) [(l.1, !l.2)]) :
    D.chainHom [(l.1, !l.2)] hl = inv (D.letterHom l) := by
  obtain ⟨P, _ | _⟩ := l
  -- The flipped letter `(P, !s)` computes to the opposite crossing; restate it as such.
  · change eqToHom _ ≫ D.letterHom (P, true) ≫ eqToHom _ = _
    simp [letterHom_true, letterHom_false]
  · change eqToHom _ ≫ D.letterHom (P, false) ≫ eqToHom _ = _
    simp [letterHom_true, letterHom_false]

/-- Reversing a chain and flipping its signs inverts its composite. -/
theorem chainHom_reverse {L : List (C.walls × Bool)}
    (hL : C.IsCrossingChain D.normal D.ker_normal a b L) :
    D.chainHom (L.reverse.map fun l => (l.1, !l.2)) hL.reverse = inv (D.chainHom L hL) := by
  induction L generalizing a with
  | nil =>
    obtain rfl : a = b := isCrossingChain_nil.mp hL
    simp [chainHom]
  | cons l L ih =>
    obtain ⟨rfl, hL'⟩ := (isCrossingChain_cons _ _).mp hL
    have hl : C.IsCrossingChain D.normal D.ker_normal (C.crossingTarget D.normal D.ker_normal l)
        (C.crossingSource D.normal D.ker_normal l) [(l.1, !l.2)] := by simp
    rw [D.chainHom_congr _ ((isCrossingChain_append).mpr ⟨_, hL'.reverse, hl⟩)
      (by rw [List.reverse_cons, List.map_append]; rfl),
      D.chainHom_append hL'.reverse hl, ih hL', D.chainHom_singleton_flip]
    simp [chainHom]

/-- Transport along an admissible path: the composite of the signed wall arrows in the
order in which the path crosses the walls. -/
def transport (p : AdmissiblePLPath x y) : D.obj (chamber x) ⟶ D.obj (chamber y) :=
  D.chainHom (p.crossingLetters D.normal) (p.isCrossingChain_crossingLetters D.normal D.ker_normal)

/-- Transport is the composite along the crossing letters of the path. -/
theorem transport_def (p : AdmissiblePLPath x y) :
    D.transport p = D.chainHom (p.crossingLetters D.normal)
      (p.isCrossingChain_crossingLetters D.normal D.ker_normal) := (rfl)

/-- A constant path transports by the identity. -/
@[simp]
theorem transport_nil : D.transport (Quiver.Path.nil : AdmissiblePLPath x x) = 𝟙 _ := by
  simp [transport_def]

/-- Transport along a concatenation is the composite of the transports, the first path
acting first. -/
@[simp]
theorem transport_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.transport (p.comp q) = D.transport p ≫ D.transport q := by
  rw [transport_def, D.chainHom_congr _ (isCrossingChain_append.mpr
      ⟨_, p.isCrossingChain_crossingLetters D.normal D.ker_normal,
        q.isCrossingChain_crossingLetters D.normal D.ker_normal⟩)
      (Quiver.Path.crossingLetters_comp p q D.normal), D.chainHom_append]
  rfl

/-- Appending a segment composes with its transport on the right. -/
@[simp]
theorem transport_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    D.transport (p.cons e) = D.transport p ≫ D.transport e.toPath := by
  rw [← Quiver.Path.comp_toPath_eq_cons, transport_comp]

/-- Transport along the reversed path is the inverse transport. -/
@[simp]
theorem transport_reverse (p : AdmissiblePLPath x y) :
    D.transport p.reverse = inv (D.transport p) := by
  rw [transport_def, D.chainHom_congr _
      (p.isCrossingChain_crossingLetters D.normal D.ker_normal).reverse
      (Quiver.Path.crossingLetters_reverse p D.normal D.ker_normal), D.chainHom_reverse]
  rfl

/-- Subdividing a path by allowed interior vertices preserves its transport. -/
theorem transport_eq_of_isSubdivision {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q) :
    D.transport q = D.transport p :=
  D.chainHom_congr _ _ (hpq.crossingLetters_eq D.normal)

/-- Relabel a diagram along a functor of groupoids, keeping its coorientations. -/
-- Reducible and exposed, so that the relabelled chamber objects compute in the types of
-- its arrows and their identities are found by `simp`.
@[expose, reducible]
def map (F : G ⥤ G') : GroupoidWallDiagram C G' where
  normal := D.normal
  ker_normal := D.ker_normal
  obj c := F.obj (D.obj c)
  label P := F.map (D.label P)

/-- Relabelling keeps the coorientations. -/
@[simp]
theorem map_normal (F : G ⥤ G') : (D.map F).normal = D.normal := (rfl)

/-- Relabelling applies the functor to the chamber objects. -/
@[simp]
theorem map_obj (F : G ⥤ G') (c : Chamber (fun P : C.walls => (P : Set V))) :
    (D.map F).obj c = F.obj (D.obj c) := (rfl)

/-- Relabelling applies the functor to the wall arrows. -/
theorem map_label (F : G ⥤ G') (P : C.walls) : (D.map F).label P = F.map (D.label P) := (rfl)

/-- Relabelling along the identity functor is the identity. -/
@[simp]
theorem map_id : D.map (𝟭 G) = D := (rfl)

/-- Relabelling along a composite functor is relabelling in two steps. -/
theorem map_comp (F : G ⥤ G') (F' : G' ⥤ G'') : D.map (F ⋙ F') = (D.map F).map F' := (rfl)

/-- Relabelling commutes with composites along chains. -/
theorem chainHom_map (F : G ⥤ G') {L : List (C.walls × Bool)}
    (hL : C.IsCrossingChain D.normal D.ker_normal a b L) :
    (D.map F).chainHom L hL = F.map (D.chainHom L hL) := by
  induction L generalizing a with
  | nil =>
    obtain rfl : a = b := isCrossingChain_nil.mp hL
    simp [chainHom]
  | cons l L ih =>
    obtain ⟨rfl, hL'⟩ := (isCrossingChain_cons _ _).mp hL
    obtain ⟨P, _ | _⟩ := l <;>
      simp [chainHom, ih hL', letterHom_true, letterHom_false]

/-- Transport of a relabelled diagram is the image of the transport. -/
@[simp]
theorem transport_map (F : G ⥤ G') (p : AdmissiblePLPath x y) :
    (D.map F).transport p = F.map (D.transport p) :=
  D.chainHom_map F _

end GroupoidWallDiagram

namespace FiniteWallDiagram

variable {C : FinitePolyhedralComplex h} {H : Type*} [Group H] (D : FiniteWallDiagram C H)
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- A group-labelled diagram as a diagram in the one-object groupoid of the group. -/
-- Reducible and exposed, so that the chamber objects compute to the unique object.
@[expose, reducible]
def toGroupoidWallDiagram : GroupoidWallDiagram C (SingleObj H) where
  normal := D.normal
  ker_normal := D.ker_normal
  obj _ := SingleObj.star H
  label P := (D.label P : SingleObj.star H ⟶ SingleObj.star H)

/-- In the one-object groupoid, a composite along a chain is the signed product of the
labels, with the first crossing rightmost. -/
theorem chainHom_toGroupoidWallDiagram {a b : Chamber (fun P : C.walls => (P : Set V))}
    {L : List (C.walls × Bool)}
    (hL : C.IsCrossingChain D.normal D.ker_normal a b L) :
    (D.toGroupoidWallDiagram.chainHom L hL : H) =
      (L.reverse.map fun l => if l.2 then (D.label l.1)⁻¹ else D.label l.1).prod := by
  induction L generalizing a with
  | nil => rfl
  | cons l L ih =>
    obtain ⟨rfl, hL'⟩ := (isCrossingChain_cons _ _).mp hL
    simp only [GroupoidWallDiagram.chainHom]
    rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, ih hL',
      List.reverse_cons, List.map_append, List.prod_append]
    obtain ⟨P, _ | _⟩ := l <;>
      simp [GroupoidWallDiagram.letterHom, SingleObj.inv_as_inv, eqToHom_refl,
        SingleObj.id_as_one]

/-- For a group-labelled diagram, groupoid transport is the path product. -/
@[simp]
theorem transport_toGroupoidWallDiagram (p : AdmissiblePLPath x y) :
    (D.toGroupoidWallDiagram.transport p : H) = D.pathProduct p := by
  rw [GroupoidWallDiagram.transport_def]
  refine (D.chainHom_toGroupoidWallDiagram _).trans ?_
  rw [pathProduct_def, Quiver.Path.crossingWord_eq_prod_crossingLetters,
    MonoidHom.map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  by_cases hl : l.2 <;> simp [hl]

end FiniteWallDiagram

end Mei
