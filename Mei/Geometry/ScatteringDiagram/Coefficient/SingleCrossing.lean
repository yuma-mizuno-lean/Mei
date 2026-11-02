/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Path

/-!
# Wall crossing of an admissible segment through a single wall

An admissible segment of a finite wall diagram crosses each wall in its relative
interior. When only one wall is crossed, the signed ordered product of Convention 3
degenerates to a single letter, so the path product is the label of that wall, inverted
exactly when the segment has positive normal velocity with respect to the coorientation.

Consequently a section of the coefficient local system obeys the facet equation
`s(Q⁺) = θ⁻¹ • s(Q⁻)` across a singly crossed wall: two off-wall values on the two sides
of one wall are related by the inverse of its label. In particular a family that takes
the same value on both sides is a section only if that value is fixed by the label, so a
wall genuinely imposes an equation on the coefficients and cannot be ignored.

These are the one-crossing computations from which the local identities at a wall are
assembled. The single-crossing product is read off from
`FiniteWallDiagram.pathProduct_toPath` through the crossing list
`FinitePolyhedralComplex.orderedCrossings`, and the value equation uses the transport of
`FiniteWallDiagram.coefficientLocalSystem_segment_of_subset`. Neither consistency nor
commutativity of the labels nor genericity of the segment is assumed. The wall-crossing
convention is that of Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public section

open Set CategoryTheory TopologicalSpace Opposite TopCat Mei.Convex

namespace Mei.FiniteWallDiagram

variable {N V H M : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : FinitePolyhedralComplex h} [Group H] (D : FiniteWallDiagram C H)
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- An admissible segment whose only geometric crossing is `(P, t)` has the crossing list
`[(P, t)]`, so its product is one signed copy of the label of `P`. -/
theorem pathProduct_toPath_eq_of_crossings_eq_singleton (e : x ⟶ y) {P : C.walls} {t : ℝ}
    (he : WallComplement.crossings x y = {(P, t)}) :
    D.pathProduct e.toPath =
      if 0 < D.normal P (y.val - x.val) then (D.label P)⁻¹ else D.label P := by
  have hord : [(P, t)] = C.orderedCrossings e := by
    rw [C.orderedCrossings_eq_iff]
    exact ⟨by simp, fun a => by rw [he]; simp⟩
  rw [pathProduct_toPath, ← hord]
  simp

/-- A single crossing with positive normal velocity contributes the inverse label. -/
theorem pathProduct_toPath_eq_inv_of_crossings_eq_singleton (e : x ⟶ y) {P : C.walls}
    {t : ℝ} (he : WallComplement.crossings x y = {(P, t)})
    (hv : 0 < D.normal P (y.val - x.val)) : D.pathProduct e.toPath = (D.label P)⁻¹ := by
  rw [D.pathProduct_toPath_eq_of_crossings_eq_singleton e he, ite_eq_left hv]

/-- A single crossing with negative normal velocity contributes the label itself. -/
theorem pathProduct_toPath_eq_of_crossings_eq_singleton_of_neg (e : x ⟶ y) {P : C.walls}
    {t : ℝ} (he : WallComplement.crossings x y = {(P, t)})
    (hv : D.normal P (y.val - x.val) < 0) : D.pathProduct e.toPath = D.label P := by
  rw [D.pathProduct_toPath_eq_of_crossings_eq_singleton e he, ite_eq_right hv.not_gt]

/-- Coefficient transport along a segment crossing one wall is the corresponding signed
label action. -/
theorem coefficientPathTransport_toPath_eq_smul_of_crossings_eq_singleton [MulAction H M]
    (e : x ⟶ y) {P : C.walls} {t : ℝ}
    (he : WallComplement.crossings x y = {(P, t)}) (a : M) :
    D.coefficientPathTransport M e.toPath a =
      (if 0 < D.normal P (y.val - x.val) then (D.label P)⁻¹ else D.label P) • a := by
  rw [coefficientPathTransport_apply, D.pathProduct_toPath_eq_of_crossings_eq_singleton e he]

section Section

variable [MulAction H M] {U : Opens C.regularSpace}

variable (x y : C.coefficientPoints) (hx : x.val ∈ U) (hy : y.val ∈ U)
  (hseg : segment ℝ x.val.val y.val.val ⊆ Subtype.val '' (U : Set C.regularSpace))
  (s : (D.coefficientLocalSystem M).presheaf.obj (op U))

include hx hy hseg in
/-- The facet equation: a section of the coefficient local system relates its values on
the two sides of a single crossed wall by the signed action of that wall's label. -/
theorem coefficientLocalSystem_value_of_crossings_eq_singleton
    (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩) {P : C.walls} {t : ℝ}
    (hcross : WallComplement.crossings
      (⟨x.val.val, x.property⟩ : WallComplement (fun Q : C.walls => (Q : Set V)))
      ⟨y.val.val, y.property⟩ = {(P, t)}) :
    (D.coefficientTransport M).value s y hy =
      (if 0 < D.normal P (y.val.val - x.val.val) then (D.label P)⁻¹ else D.label P) •
        (D.coefficientTransport M).value s x hx := by
  have h := D.coefficientLocalSystem_segment_of_subset x y hx hy e hseg M s
  rw [coefficientPathTransport_apply,
    D.pathProduct_toPath_eq_of_crossings_eq_singleton e hcross] at h
  exact h.symm

include hx hy hseg in
/-- Across a wall on which the traversal has positive normal velocity, a section's value
is the inverse label applied to its value on the other side. -/
theorem coefficientLocalSystem_value_eq_inv_smul
    (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩) {P : C.walls} {t : ℝ}
    (hcross : WallComplement.crossings
      (⟨x.val.val, x.property⟩ : WallComplement (fun Q : C.walls => (Q : Set V)))
      ⟨y.val.val, y.property⟩ = {(P, t)})
    (hv : 0 < D.normal P (y.val.val - x.val.val)) :
    (D.coefficientTransport M).value s y hy =
      (D.label P)⁻¹ • (D.coefficientTransport M).value s x hx := by
  rw [D.coefficientLocalSystem_value_of_crossings_eq_singleton x y hx hy hseg s e hcross,
    ite_eq_left hv]

include hx hy hseg in
/-- Across a wall on which the traversal has negative normal velocity, a section's value
is the label applied to its value on the other side. -/
theorem coefficientLocalSystem_value_eq_smul
    (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩) {P : C.walls} {t : ℝ}
    (hcross : WallComplement.crossings
      (⟨x.val.val, x.property⟩ : WallComplement (fun Q : C.walls => (Q : Set V)))
      ⟨y.val.val, y.property⟩ = {(P, t)})
    (hv : D.normal P (y.val.val - x.val.val) < 0) :
    (D.coefficientTransport M).value s y hy =
      D.label P • (D.coefficientTransport M).value s x hx := by
  rw [D.coefficientLocalSystem_value_of_crossings_eq_singleton x y hx hy hseg s e hcross,
    ite_eq_right hv.not_gt]

include hx hy hseg in
/-- If a section takes the same value `a` on the two sides of a crossed wall, the label of
that wall fixes `a`. -/
theorem label_smul_eq_self_of_value_eq
    (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩) {P : C.walls} {t : ℝ}
    (hcross : WallComplement.crossings
      (⟨x.val.val, x.property⟩ : WallComplement (fun Q : C.walls => (Q : Set V)))
      ⟨y.val.val, y.property⟩ = {(P, t)})
    (hv : 0 < D.normal P (y.val.val - x.val.val)) (a : M)
    (hxval : (D.coefficientTransport M).value s x hx = a)
    (hyval : (D.coefficientTransport M).value s y hy = a) : D.label P • a = a := by
  have h : a = (D.label P)⁻¹ • a := by
    simpa only [hxval, hyval] using
      D.coefficientLocalSystem_value_eq_inv_smul x y hx hy hseg s e hcross hv
  calc D.label P • a = D.label P • ((D.label P)⁻¹ • a) := congrArg (D.label P • ·) h
    _ = a := by rw [← mul_smul, mul_inv_cancel, one_smul]

include hx hy hseg in
/-- A family that takes the same value `a` on the two sides of a crossed wall is a section
of the coefficient local system only if the label fixes `a`. -/
theorem not_value_eq_and_value_eq_of_smul_ne
    (e : (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩) {P : C.walls} {t : ℝ}
    (hcross : WallComplement.crossings
      (⟨x.val.val, x.property⟩ : WallComplement (fun Q : C.walls => (Q : Set V)))
      ⟨y.val.val, y.property⟩ = {(P, t)})
    (hv : 0 < D.normal P (y.val.val - x.val.val)) {a : M} (hne : D.label P • a ≠ a) :
    ¬ ((D.coefficientTransport M).value s x hx = a ∧
        (D.coefficientTransport M).value s y hy = a) := by
  rintro ⟨hxval, hyval⟩
  exact hne (D.label_smul_eq_self_of_value_eq x y hx hy hseg s e hcross hv a hxval hyval)

end Section

end Mei.FiniteWallDiagram
