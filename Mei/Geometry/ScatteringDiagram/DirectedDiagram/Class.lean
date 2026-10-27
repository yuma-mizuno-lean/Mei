/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Equivalence

/-!
# Classes of indexed directed diagrams

Bundle the index type of a directed diagram before taking its equivalence class.
Finite-order classes identify precisely the common path products at that order;
completed classes are determined by all their finite-order projections. Changing
Lie coefficients acts on both kinds of classes, even when labels disappear.

The quotient constructions use `DirectedDiagram.Equivalent` and
`DirectedDiagram.LevelEquivalent`, including their coefficient-map and cutoff
compatibility. The bundling follows `Mei.ConsistentDiagram` for KS diagrams,
while retaining arbitrary directed presentations and a fixed universe of indices.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v w

variable {Γ Λ R V : Type*} {L L' : Type v}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}

/-- A directed diagram together with its index type in a fixed universe. -/
structure Presentation (h : TauCeti.Toric.IsIntegralLattice i)
    (H : DirectedWallSpaces ρ ℒ) where
  /-- The type of indexed wall occurrences. -/
  Index : Type u
  /-- The finitely active wall family. -/
  diagram : DirectedDiagram (d := d) h H Index

/-- Equality of all finite common path products on bundled presentations. -/
def Presentation.setoid : Setoid (Presentation.{u} (d := d) h H) where
  r D E := D.diagram.Equivalent E.diagram
  iseqv := ⟨fun D => Equivalent.refl D.diagram,
    fun hDE => hDE.symm, fun hDE hEF => hDE.trans hEF⟩

/-- Equality of common path products at a specified cutoff. -/
def Presentation.levelSetoid (k : ℕ) : Setoid (Presentation.{u} (d := d) h H) where
  r D E := D.diagram.LevelEquivalent E.diagram k
  iseqv := ⟨fun D => LevelEquivalent.refl D.diagram k,
    fun hDE => hDE.symm, fun hDE hEF => hDE.trans hEF⟩

/-- Indexed directed diagrams modulo agreement of all finite path products. -/
def Class : Type _ := Quotient (Presentation.setoid.{u} (d := d) (h := h) (H := H))

/-- Indexed directed diagrams modulo agreement of order-`k` path products. -/
def LevelClass (k : ℕ) : Type _ :=
  Quotient (Presentation.levelSetoid.{u} (d := d) (h := h) (H := H) k)

variable {ι κ : Type u}

/-- The completed equivalence class of an indexed directed diagram. -/
def toClass (D : DirectedDiagram (d := d) h H ι) : Class (d := d) (h := h) (H := H) :=
  Quotient.mk _ ⟨ι, D⟩

/-- The finite-order equivalence class of an indexed directed diagram. -/
def toLevelClass (D : DirectedDiagram (d := d) h H ι) (k : ℕ) :
    LevelClass (d := d) (h := h) (H := H) k := Quotient.mk _ ⟨ι, D⟩

/-- Equality of completed classes is exactly diagram equivalence. -/
@[simp]
theorem toClass_eq_iff (D : DirectedDiagram (d := d) h H ι)
    (E : DirectedDiagram (d := d) h H κ) : D.toClass = E.toClass ↔ D.Equivalent E :=
  Quotient.eq

/-- Equality of finite-order classes is exactly equivalence at that cutoff. -/
@[simp]
theorem toLevelClass_eq_iff (D : DirectedDiagram (d := d) h H ι)
    (E : DirectedDiagram (d := d) h H κ) (k : ℕ) :
    D.toLevelClass k = E.toLevelClass k ↔ D.LevelEquivalent E k := Quotient.eq

/-- Prove a property of completed classes on indexed representatives. -/
@[elab_as_elim]
theorem Class.inductionOn {p : Class.{u} (d := d) (h := h) (H := H) → Prop}
    (x : Class.{u} (d := d) (h := h) (H := H))
    (hp : ∀ {ι : Type u} (D : DirectedDiagram (d := d) h H ι), p D.toClass) : p x :=
  Quotient.inductionOn x (fun D => hp D.diagram)

/-- Prove a property of finite-order classes on indexed representatives. -/
@[elab_as_elim]
theorem LevelClass.inductionOn {k : ℕ}
    {p : LevelClass.{u} (d := d) (h := h) (H := H) k → Prop}
    (x : LevelClass.{u} (d := d) (h := h) (H := H) k)
    (hp : ∀ {ι : Type u} (D : DirectedDiagram (d := d) h H ι), p (D.toLevelClass k)) : p x :=
  Quotient.inductionOn x (fun D => hp D.diagram)

/-- Descend a presentation-independent function to completed classes. -/
def Class.lift {α : Sort w}
    (f : ∀ {ι : Type u}, DirectedDiagram (d := d) h H ι → α)
    (hf : ∀ {ι κ : Type u} (D : DirectedDiagram (d := d) h H ι)
      (E : DirectedDiagram (d := d) h H κ), D.Equivalent E → f D = f E) :
    Class.{u} (d := d) (h := h) (H := H) → α :=
  Quotient.lift (fun D => f D.diagram) (fun D E => hf D.diagram E.diagram)

@[simp]
theorem Class.lift_toClass {α : Sort w}
    (f : ∀ {ι : Type u}, DirectedDiagram (d := d) h H ι → α)
    (hf : ∀ {ι κ : Type u} (D : DirectedDiagram (d := d) h H ι)
      (E : DirectedDiagram (d := d) h H κ), D.Equivalent E → f D = f E)
    (D : DirectedDiagram (d := d) h H ι) : lift @f @hf D.toClass = f D := (rfl)

/-- Descend a function invariant under order-`k` equivalence to finite-order classes. -/
def LevelClass.lift {α : Sort w} (k : ℕ)
    (f : ∀ {ι : Type u}, DirectedDiagram (d := d) h H ι → α)
    (hf : ∀ {ι κ : Type u} (D : DirectedDiagram (d := d) h H ι)
      (E : DirectedDiagram (d := d) h H κ), D.LevelEquivalent E k → f D = f E) :
    LevelClass.{u} (d := d) (h := h) (H := H) k → α :=
  Quotient.lift (fun D => f D.diagram) (fun D E => hf D.diagram E.diagram)

@[simp]
theorem LevelClass.lift_toLevelClass {α : Sort w} (k : ℕ)
    (f : ∀ {ι : Type u}, DirectedDiagram (d := d) h H ι → α)
    (hf : ∀ {ι κ : Type u} (D : DirectedDiagram (d := d) h H ι)
      (E : DirectedDiagram (d := d) h H κ), D.LevelEquivalent E k → f D = f E)
    (D : DirectedDiagram (d := d) h H ι) : lift k @f @hf (D.toLevelClass k) = f D := (rfl)

/-- Forget all orders above a fixed cutoff in a completed class. -/
def Class.projection (k : ℕ) : Class (d := d) (h := h) (H := H) →
    LevelClass (d := d) (h := h) (H := H) k :=
  Class.lift (fun D => D.toLevelClass k)
    (fun _ _ hDE => (toLevelClass_eq_iff _ _ k).mpr ((equivalent_iff _ _).mp hDE k))

@[simp]
theorem Class.projection_toClass (D : DirectedDiagram (d := d) h H ι) (k : ℕ) :
    Class.projection k D.toClass = D.toLevelClass k := (rfl)

/-- A completed class is determined by its finite-order classes. -/
@[ext]
theorem Class.ext {x y : Class.{u} (d := d) (h := h) (H := H)}
    (he : ∀ k, x.projection k = y.projection k) : x = y := by
  induction x using Quotient.inductionOn with | _ D =>
    induction y using Quotient.inductionOn with | _ E =>
      exact Quotient.sound ((equivalent_iff _ _).mpr
        (fun k => (toLevelClass_eq_iff _ _ k).mp (he k)))

/-- Lower the cutoff of a finite-order class. -/
def LevelClass.project {k l : ℕ} (hkl : k ≤ l) :
    LevelClass.{u} (d := d) (h := h) (H := H) l →
      LevelClass.{u} (d := d) (h := h) (H := H) k :=
  LevelClass.lift l (fun D => D.toLevelClass k)
    (fun _ _ hDE => (toLevelClass_eq_iff _ _ k).mpr (hDE.mono hkl))

@[simp]
theorem LevelClass.project_toLevelClass (D : DirectedDiagram (d := d) h H ι)
    {k l : ℕ} (hkl : k ≤ l) :
    LevelClass.project hkl (D.toLevelClass l) = D.toLevelClass k := (rfl)

@[simp]
theorem LevelClass.project_refl (k : ℕ)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) k) : project (le_refl k) x = x := by
  induction x using Quotient.inductionOn with | _ D => rfl

/-- Successive cutoff projections compose. -/
@[simp]
theorem LevelClass.project_project {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) m) :
    project hkl (project hlm x) = project (hkl.trans hlm) x := by
  induction x using Quotient.inductionOn with | _ D => rfl

@[simp]
theorem Class.project_projection {k l : ℕ} (hkl : k ≤ l)
    (x : Class.{u} (d := d) (h := h) (H := H)) :
    LevelClass.project hkl (x.projection l) = x.projection k := by
  induction x using Quotient.inductionOn with | _ D => rfl

variable (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

/-- Change coefficients of a completed class without choosing a presentation. -/
def Class.map : Class.{u} (d := d) (h := h) (H := H) →
    Class.{u} (d := d) (h := h) (H := H') :=
  Class.lift (fun D => (D.map f hf).toClass)
    (fun _ _ hDE => (toClass_eq_iff _ _).mpr (hDE.map f hf))

/-- Change coefficients of a finite-order class. -/
def LevelClass.map (k : ℕ) : LevelClass.{u} (d := d) (h := h) (H := H) k →
    LevelClass.{u} (d := d) (h := h) (H := H') k :=
  LevelClass.lift k (fun D => (D.map f hf).toLevelClass k)
    (fun _ _ hDE => (toLevelClass_eq_iff _ _ k).mpr (hDE.map f hf))

@[simp]
theorem Class.map_toClass (D : DirectedDiagram (d := d) h H ι) :
    Class.map f hf D.toClass = (D.map f hf).toClass := (rfl)

@[simp]
theorem LevelClass.map_toLevelClass (D : DirectedDiagram (d := d) h H ι) (k : ℕ) :
    LevelClass.map f hf k (D.toLevelClass k) = (D.map f hf).toLevelClass k := (rfl)

@[simp]
theorem Class.projection_map (k : ℕ) (x : Class.{u} (d := d) (h := h) (H := H)) :
    (map f hf x).projection k = LevelClass.map f hf k (x.projection k) := by
  induction x using Quotient.inductionOn with | _ D => rfl

/-- Lowering the cutoff commutes with changing coefficients. -/
@[simp]
theorem LevelClass.project_map {k l : ℕ} (hkl : k ≤ l)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) l) :
    project hkl (map f hf l x) = map f hf k (project hkl x) := by
  induction x using Quotient.inductionOn with | _ D => rfl

/-- The identity coefficient map fixes completed classes. -/
@[simp]
theorem Class.map_id (x : Class.{u} (d := d) (h := h) (H := H)) :
    map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) x = x := by
  induction x using Class.inductionOn with | _ D =>
    simp only [map_toClass, DirectedDiagram.map_id]

/-- The identity coefficient map fixes finite-order classes. -/
@[simp]
theorem LevelClass.map_id (k : ℕ) (x : LevelClass.{u} (d := d) (h := h) (H := H) k) :
    map (GradedLieHom.id ℒ) (fun _ _ _ hx => by simpa using hx) k x = x := by
  induction x using LevelClass.inductionOn with | _ D =>
    simp only [map_toLevelClass, DirectedDiagram.map_id]

variable {L'' : Type v} [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L'']
  [IsScalarTower ℚ R L''] {ℋ : Γ → Submodule R L''}
  [GradedLieAlgebra ℋ] [IsPositiveGrading d ℋ] {H'' : DirectedWallSpaces ρ ℋ}
  (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
  (hg : ∀ n m, ∀ x ∈ H'.wall n m, g x ∈ H''.wall n m)

/-- Successive coefficient maps compose on completed classes. -/
@[simp]
theorem Class.map_map (x : Class.{u} (d := d) (h := h) (H := H)) :
    map g hg (map f hf x) = map
      { toLieHom := g.toLieHom.comp f.toLieHom
        map_mem hx := by simpa using g.map_mem (f.map_mem hx) }
      (fun n m x hx => hg n m _ (hf n m x hx)) x := by
  induction x using Class.inductionOn with | _ D =>
    exact congrArg toClass (D.map_map f hf g hg)

/-- Successive coefficient maps compose on finite-order classes. -/
@[simp]
theorem LevelClass.map_map (k : ℕ)
    (x : LevelClass.{u} (d := d) (h := h) (H := H) k) :
    map g hg k (map f hf k x) = map
      { toLieHom := g.toLieHom.comp f.toLieHom
        map_mem hx := by simpa using g.map_mem (f.map_mem hx) }
      (fun n m x hx => hg n m _ (hf n m x hx)) k x := by
  induction x using LevelClass.inductionOn with | _ D =>
    exact congrArg (fun E => E.toLevelClass k) (D.map_map f hf g hg)

end Mei.DirectedDiagram
