/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Class

/-!
# Coordinate changes on directed-diagram classes

Integral affine coordinate changes and compatible graded Lie equivalences act on
presentation-independent diagram classes. At finite order the source cutoff need
only cover the target cutoff through the coordinate modulus. Enlarging that source
cutoff or lowering the target cutoff commutes with transport. At all orders transport
is an equivalence, with inverse given by the inverse coordinates.

The constructions descend `DirectedDiagram.image` using `Equivalent.image` and
`LevelEquivalent.image`; no representative or common wall indexing is selected.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v

variable {Γ Γ' Γ'' Λ Λ' Λ'' R V V' V'' : Type*} {L L' L'' : Type v}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
  {i : Λ →+ V} {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Transport a completed diagram class through compatible affine coordinates. -/
def Class.image : Class.{u} (d := d) (h := h) (H := H) →
    Class.{u} (d := d') (h := h') (H := H') :=
  Class.lift (fun D => (D.image e E hE).toClass)
    (fun _ _ hDF => (toClass_eq_iff _ _).mpr (hDF.image (e := e) (E := E) (hE := hE)))

/-- Transport a finite-order class from any source cutoff covering the target modulus. -/
def LevelClass.image (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a) :
    LevelClass.{u} (d := d) (h := h) (H := H) a →
      LevelClass.{u} (d := d') (h := h') (H := H') k :=
  LevelClass.lift a (fun D => (D.image e E hE).toLevelClass k)
    (fun _ _ hDF => (toLevelClass_eq_iff _ _ k).mpr
      (hDF.image (e := e) (E := E) (hE := hE) ha))

@[simp]
theorem Class.image_toClass {ι : Type u} (D : DirectedDiagram (d := d) h H ι) :
    Class.image e E hE D.toClass = (D.image e E hE).toClass := by
  simp only [image, lift_toClass]

@[simp]
theorem LevelClass.image_toLevelClass {ι : Type u}
    (D : DirectedDiagram (d := d) h H ι) (k : ℕ) {a : ℕ}
    (ha : E.degreeMap.modulus k ≤ a) :
    LevelClass.image e E hE k ha (D.toLevelClass a) =
      (D.image e E hE).toLevelClass k := by
  simp only [image, lift_toLevelClass]

/-- Completed transport is computed at any sufficiently fine source projection. -/
theorem Class.projection_image_of_le (k : ℕ) {a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (x : Class.{u} (d := d) (h := h) (H := H)) :
    (image e E hE x).projection k = LevelClass.image e E hE k ha (x.projection a) := by
  induction x using Class.inductionOn with | _ D =>
    simp only [image_toClass, projection_toClass, LevelClass.image_toLevelClass]

/-- Project transported classes at the canonical source cutoff. -/
@[simp]
theorem Class.projection_image (k : ℕ)
    (x : Class.{u} (d := d) (h := h) (H := H)) :
    (image e E hE x).projection k =
      LevelClass.image e E hE k le_rfl (x.projection (E.degreeMap.modulus k)) :=
  projection_image_of_le e E hE k le_rfl x

/-- Extra source orders do not affect finite-order transport. -/
@[simp]
theorem LevelClass.image_project {k a b : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hab : a ≤ b) (x : LevelClass.{u} (d := d) (h := h) (H := H) b) :
    image e E hE k ha (project hab x) = image e E hE k (ha.trans hab) x := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [project_toLevelClass, image_toLevelClass]

/-- Lowering the target order commutes with finite-order transport. -/
@[simp]
theorem LevelClass.project_image {k l a : ℕ} (hkl : k ≤ l)
    (ha : E.degreeMap.modulus l ≤ a)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) a) :
    project hkl (image e E hE l ha x) =
      image e E hE k ((E.degreeMap.monotone_modulus hkl).trans ha) x := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [image_toLevelClass, project_toLevelClass]

/-- Identity coordinates fix completed diagram classes. -/
@[simp]
theorem Class.image_refl (x : Class.{u} (d := d) (h := h) (H := H)) :
    image (Toric.IntegralAffineEquiv.refl h)
      (DirectedWallSpaces.CoordinateChange.refl H) (by simp) x = x := by
  induction x using Class.inductionOn with | _ D =>
    simp only [image_toClass, DirectedDiagram.image_refl]

/-- Identity coordinates fix each finite-order class. -/
@[simp]
theorem LevelClass.image_refl (k : ℕ)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) k) :
    image (Toric.IntegralAffineEquiv.refl h)
      (DirectedWallSpaces.CoordinateChange.refl H) (by simp) k (by
        rw [DirectedWallSpaces.CoordinateChange.degreeMap_modulus_le_iff]
        intro n _ hn
        simpa using hn) x = x := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [image_toLevelClass, DirectedDiagram.image_refl]

variable (f : Toric.IntegralAffineEquiv h' h'')
  (F : DirectedWallSpaces.CoordinateChange (d := d') (e := d'') H' H'')
  (hF : F.tangentEquiv = f.latticeEquiv)

/-- Successive coordinate changes compose on completed classes. -/
@[simp]
theorem Class.image_image (x : Class.{u} (d := d) (h := h) (H := H)) :
    image f F hF (image e E hE x) = image (e.trans f) (E.trans F) (by simp [hE, hF]) x := by
  induction x using Class.inductionOn with | _ D =>
    simp only [image_toClass, DirectedDiagram.image_image]

/-- Coordinate changes identify completed classes, including changes of positive degree. -/
def Class.imageEquiv : Class.{u} (d := d) (h := h) (H := H) ≃
    Class.{u} (d := d') (h := h') (H := H') where
  toFun := image e E hE
  invFun := image e.symm E.symm (by simp [hE])
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem Class.imageEquiv_apply (x : Class.{u} (d := d) (h := h) (H := H)) :
    imageEquiv e E hE x = image e E hE x := (rfl)

@[simp]
theorem Class.imageEquiv_symm_apply (x : Class.{u} (d := d') (h := h') (H := H')) :
    (imageEquiv e E hE).symm x = image e.symm E.symm (by simp [hE]) x := (rfl)

/-- Finite coordinate changes compose at any cutoffs covering their respective moduli. -/
theorem LevelClass.image_image {k b a : ℕ}
    (hb : F.degreeMap.modulus k ≤ b) (ha : E.degreeMap.modulus b ≤ a)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) a) :
    image f F hF k hb (image e E hE b ha x) =
      image (e.trans f) (E.trans F) (by simp [hE, hF]) k (by
        rw [DirectedWallSpaces.CoordinateChange.degreeMap_modulus_le_iff]
        intro n hn hnk
        apply (E.degreeMap_modulus_le_iff b a).mp ha n hn
        apply (F.degreeMap_modulus_le_iff k b).mp hb (E.degreeEquiv n)
          ((E.monoid_mem_iff n).mpr hn)
        simpa using hnk) x := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [image_toLevelClass, DirectedDiagram.image_image]

end Mei.DirectedDiagram
