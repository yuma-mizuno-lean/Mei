/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Cylinder.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Class

/-!
# Cylinder maps of scattering-diagram classes

Cylinder lifting descends to injective maps of finite-order and completed
directed-diagram classes. The maps commute with all cutoff projections. Thus
identifying diagrams after adjoining unrestricted coordinates is equivalent to
identifying their projected diagrams, without choosing a wall presentation.

We use `Class.lift` and `LevelClass.lift` with the preservation and reflection of
equivalence for cylinders. The underlying geometric comparison occurs in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v

variable {Γ Λ K R V E : Type*} {L : Type v}
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup K]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ Λ × K} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {j : K →+ E} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (h' : TauCeti.Toric.IsIntegralLattice j)

/-- Lift a completed diagram class to cylinders, independently of its presentation. -/
def Class.cylinder :
    Class.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K)) →
      Class.{u} (d := d) (h := h.prod h') (H := H) :=
  Class.lift (fun D => (D.cylinder h').toClass)
    (fun _ _ hDF => (toClass_eq_iff _ _).mpr (hDF.cylinder h'))

/-- Lift a finite-order diagram class to cylinders at the same order. -/
def LevelClass.cylinder (k : ℕ) :
    LevelClass.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K)) k →
      LevelClass.{u} (d := d) (h := h.prod h') (H := H) k :=
  LevelClass.lift k (fun D => (D.cylinder h').toLevelClass k)
    (fun _ _ hDF => (toLevelClass_eq_iff _ _ k).mpr (hDF.cylinder h'))

/-- The completed cylinder map is computed by lifting any representative. -/
@[simp]
theorem Class.cylinder_toClass {ι : Type u}
    (D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι) :
    Class.cylinder h' D.toClass = (D.cylinder h').toClass := by
  simp only [cylinder, lift_toClass]

/-- The finite cylinder map is computed by lifting any representative. -/
@[simp]
theorem LevelClass.cylinder_toLevelClass {ι : Type u}
    (D : DirectedDiagram (d := d) h (H.project (AddMonoidHom.fst Λ K)) ι) (k : ℕ) :
    LevelClass.cylinder h' k (D.toLevelClass k) = (D.cylinder h').toLevelClass k := by
  simp only [cylinder, lift_toLevelClass]

/-- Adding unrestricted coordinates loses no completed path-product information. -/
theorem Class.cylinder_injective : Function.Injective
    (Class.cylinder.{u} (d := d) (h := h) (H := H) h') := by
  intro x y
  induction x using Class.inductionOn with | _ D =>
    induction y using Class.inductionOn with | _ F =>
      intro he
      simp only [cylinder_toClass, toClass_eq_iff, cylinder_equivalent_iff] at he
      exact (toClass_eq_iff D F).mpr he

/-- Two completed cylinder classes agree exactly when their original classes agree. -/
@[simp]
theorem Class.cylinder_inj
    {x y : Class.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K))} :
    Class.cylinder h' x = Class.cylinder h' y ↔ x = y :=
  (cylinder_injective h').eq_iff

/-- Adding unrestricted coordinates loses no finite-order path-product information. -/
theorem LevelClass.cylinder_injective (k : ℕ) : Function.Injective
    (LevelClass.cylinder.{u} (d := d) (h := h) (H := H) h' k) := by
  intro x y
  induction x using LevelClass.inductionOn with | _ D =>
    induction y using LevelClass.inductionOn with | _ F =>
      intro he
      simp only [cylinder_toLevelClass, toLevelClass_eq_iff, cylinder_levelEquivalent_iff] at he
      exact (toLevelClass_eq_iff D F k).mpr he

/-- Two finite cylinder classes agree exactly when their original classes agree. -/
@[simp]
theorem LevelClass.cylinder_inj (k : ℕ)
    {x y : LevelClass.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K)) k} :
    LevelClass.cylinder h' k x = LevelClass.cylinder h' k y ↔ x = y :=
  (cylinder_injective h' k).eq_iff

/-- Taking a finite projection commutes with cylinder lifting. -/
@[simp]
theorem Class.projection_cylinder (k : ℕ)
    (x : Class.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K))) :
    (cylinder h' x).projection k = LevelClass.cylinder h' k (x.projection k) := by
  induction x using Class.inductionOn with | _ D =>
    simp only [cylinder_toClass, projection_toClass, LevelClass.cylinder_toLevelClass]

/-- Lowering the finite cutoff commutes with cylinder lifting. -/
@[simp]
theorem LevelClass.project_cylinder {k l : ℕ} (hkl : k ≤ l)
    (x : LevelClass.{u} (d := d) (h := h) (H := H.project (AddMonoidHom.fst Λ K)) l) :
    project hkl (cylinder h' l x) = cylinder h' k (project hkl x) := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [cylinder_toLevelClass, project_toLevelClass]

end Mei.DirectedDiagram
