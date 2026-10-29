/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Finite
public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Regular
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Coefficient transport in a finite wall diagram

Group labels acting on a type transport coefficients along admissible polygonal
paths. The first crossing acts first, and subdivision leaves transport unchanged.
For a triangle whose convex hull misses singular support, the two successive
segment transports equal the direct segment transport. This follows from the
free-group crossing-word identity, without assuming global consistency or
commutativity of the wall labels. `MulAction.toPerm` supplies the coefficient
equivalence, and the existing path-product laws give its basic functoriality.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V H M : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group H] (D : FiniteWallDiagram C H)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

/-- Segment path products satisfy the cocycle law on every filled triangle
missing singular support. Wall labels may lie in an arbitrary group. -/
theorem pathProduct_mul_eq_of_regular_triangle (e : x ⟶ y) (g : y ⟶ z) (d : x ⟶ z)
    (hreg : Disjoint (convexHull ℝ {x.val, y.val, z.val})
      (singularSupport (fun P : C.walls => (P : Set V)))) :
    D.pathProduct g.toPath * D.pathProduct e.toPath = D.pathProduct d.toPath := by
  simp only [pathProduct_def, Quiver.Hom.toPath, Quiver.Path.crossingWord_cons,
    Quiver.Path.crossingWord_nil, mul_one]
  rw [← map_mul, C.segmentCrossingWord_mul_eq_of_regular_triangle D.normal D.ker_normal e g d hreg]

variable (M) [MulAction H M]

/-- Transport coefficients by the signed ordered product of the wall crossings. -/
def coefficientPathTransport (p : AdmissiblePLPath x y) : M ≃ M :=
  MulAction.toPerm (D.pathProduct p)

/-- Coefficient transport is the given group action of the path product. -/
@[simp]
theorem coefficientPathTransport_apply (p : AdmissiblePLPath x y) (a : M) :
    D.coefficientPathTransport M p a = D.pathProduct p • a := (rfl)

/-- Inverse coefficient transport acts by the inverse path product. -/
@[simp]
theorem coefficientPathTransport_symm_apply (p : AdmissiblePLPath x y) (a : M) :
    (D.coefficientPathTransport M p).symm a = (D.pathProduct p)⁻¹ • a := (rfl)

/-- A constant path preserves every coefficient. -/
@[simp]
theorem coefficientPathTransport_nil :
    D.coefficientPathTransport M (Quiver.Path.nil : AdmissiblePLPath x x) = Equiv.refl M := by
  ext a
  simp

/-- Successive paths transport coefficients in traversal order. -/
@[simp]
theorem coefficientPathTransport_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.coefficientPathTransport M (p.comp q) =
      (D.coefficientPathTransport M p).trans (D.coefficientPathTransport M q) := by
  ext a
  simp [mul_smul]

/-- Appending a segment transports along the previous path and then that segment. -/
@[simp]
theorem coefficientPathTransport_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    D.coefficientPathTransport M (p.cons e) =
      (D.coefficientPathTransport M p).trans (D.coefficientPathTransport M e.toPath) := by
  ext a
  simp only [Equiv.trans_apply, coefficientPathTransport_apply, pathProduct_cons, mul_smul]

/-- Reversing a path inverts its coefficient transport. -/
@[simp]
theorem coefficientPathTransport_reverse (p : AdmissiblePLPath x y) :
    D.coefficientPathTransport M p.reverse = (D.coefficientPathTransport M p).symm := by
  ext a
  simp

/-- Inserting allowed subdivision vertices preserves coefficient transport. -/
theorem coefficientPathTransport_eq_of_isSubdivision {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) :
    D.coefficientPathTransport M p = D.coefficientPathTransport M q := by
  unfold coefficientPathTransport
  rw [D.pathProduct_eq_of_isSubdivision hpq]

/-- The coefficient segment cocycle on a filled triangle avoiding singular support. -/
theorem coefficientPathTransport_triangle (e : x ⟶ y) (g : y ⟶ z) (d : x ⟶ z)
    (hreg : Disjoint (convexHull ℝ {x.val, y.val, z.val})
      (singularSupport (fun P : C.walls => (P : Set V)))) :
    (D.coefficientPathTransport M e.toPath).trans (D.coefficientPathTransport M g.toPath) =
      D.coefficientPathTransport M d.toPath := by
  ext a
  simp only [Equiv.trans_apply, coefficientPathTransport_apply, ← mul_smul,
    D.pathProduct_mul_eq_of_regular_triangle e g d hreg]

end Mei.FiniteWallDiagram
