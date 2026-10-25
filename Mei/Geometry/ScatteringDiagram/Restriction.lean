/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Finite
public import Mei.Geometry.Convex.PolyhedralComplex.WallDeletion

/-!
# Restricting finite wall diagrams

A diagram restricts to any complex whose walls are among its walls, retaining
coorientations and labels. If every deleted wall has identity label, restriction
preserves the product on every common admissible polygonal path. Here these are
exactly the paths admissible for the larger wall family: forgetting walls keeps
their vertices and affine segments. In particular, consistency of the restricted
diagram implies consistency of the original diagram.

Restriction respects successive wall inclusions and relabelling. The comparison
uses `Quiver.Path.crossingWord_restrict` and Mathlib's universal property
`FreeGroup.lift_unique`; no perturbation of the path is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C C' C'' : FinitePolyhedralComplex h} {H K : Type*}

/-- Restrict a diagram to a complex with fewer walls, retaining the actual normals
and labels. In particular, a subcomplex inclusion supplies `hW` via `walls_subset`. -/
def restrict (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls) :
    FiniteWallDiagram C' H where
  normal P := D.normal ⟨P.val, hW P.property⟩
  ker_normal P := D.ker_normal ⟨P.val, hW P.property⟩
  label P := D.label ⟨P.val, hW P.property⟩

@[simp]
theorem restrict_normal (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls)
    (P : C'.walls) : (D.restrict hW).normal P = D.normal ⟨P.val, hW P.property⟩ := (rfl)

@[simp]
theorem restrict_label (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls)
    (P : C'.walls) : (D.restrict hW).label P = D.label ⟨P.val, hW P.property⟩ := (rfl)

/-- Retaining all walls leaves the diagram unchanged. -/
@[simp]
theorem restrict_self (D : FiniteWallDiagram C H) :
    D.restrict (fun _ hP => hP) = D := by
  ext <;> rfl

/-- Successive restrictions retain the same wall data as a single restriction. -/
@[simp]
theorem restrict_restrict (D : FiniteWallDiagram C H)
    (hW : C'.walls ⊆ C.walls) (hW' : C''.walls ⊆ C'.walls) :
    (D.restrict hW).restrict hW' = D.restrict (hW'.trans hW) := by
  ext <;> rfl

variable [Group H] [Group K]

/-- Restriction commutes with homomorphisms of wall labels. -/
@[simp]
theorem restrict_relabel (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls)
    (f : H →* K) : (D.relabel f).restrict hW = (D.restrict hW).relabel f := by
  ext <;> simp only [restrict_normal, relabel_normal, restrict_label, relabel_label]

variable (D : FiniteWallDiagram C H) (hW : C'.walls ⊆ C.walls)

private theorem lift_label_wallDeletion
    (hlabel : ∀ P : C.walls, P.val ∉ C'.walls → D.label P = 1)
    (g : FreeGroup C.walls) :
    FreeGroup.lift (D.restrict hW).label (C.wallDeletion C' g) =
      FreeGroup.lift D.label g := by
  apply FreeGroup.lift_unique ((FreeGroup.lift (D.restrict hW).label).comp (C.wallDeletion C'))
  intro P
  simp only [MonoidHom.comp_apply, FinitePolyhedralComplex.wallDeletion_of]
  split_ifs with hP
  · simp
  · simp [hlabel P hP]

/-- Deleting identity-labelled walls preserves every common admissible path product.
The path on the smaller family has exactly the same vertices and affine segments. -/
@[simp]
theorem pathProduct_restrict
    (hlabel : ∀ P : C.walls, P.val ∉ C'.walls → D.label P = 1)
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    (D.restrict hW).pathProduct
      ((WallComplement.restrictPrefunctor (fun P : C.walls => (P : Set V))
        (fun P : C'.walls => (⟨P.val, hW P.property⟩ : C.walls))).mapPath p) =
      D.pathProduct p := by
  rw [pathProduct_def, pathProduct_def]
  have hnormal : (D.restrict hW).normal =
      fun P => D.normal ⟨P.val, hW P.property⟩ := funext (D.restrict_normal hW)
  rw [hnormal, Quiver.Path.crossingWord_restrict]
  exact D.lift_label_wallDeletion hW hlabel _

/-- A consistent restriction retaining all nonidentity labels makes the original
diagram consistent. This direction requires no path perturbation theorem. -/
theorem consistent_of_restrict
    (hlabel : ∀ P : C.walls, P.val ∉ C'.walls → D.label P = 1)
    (hc : (D.restrict hW).Consistent) : D.Consistent := by
  apply D.consistent_def.mpr
  intro x y p q
  rw [← D.pathProduct_restrict hW hlabel p, ← D.pathProduct_restrict hW hlabel q]
  exact (consistent_def _).mp hc _ _

end Mei.FiniteWallDiagram
