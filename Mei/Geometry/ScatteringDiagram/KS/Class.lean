/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Classification
public import Mei.Geometry.ScatteringDiagram.KS.Completion.Map
public import Mei.Algebra.Lie.BCH.Coordinates

/-!
# Equivalence classes of consistent KS diagrams

Consistent diagrams may have different finite complexes at every order. Their quotient
identifies diagrams precisely when all finite common path products agree. Chamber
transport is well defined on this quotient and, on the continuous-dual KS space,
`PositiveDegrees.reconstructionEquiv` identifies it with the completed BCH group.
The inverse sends an element to the class of its middle-factor reconstruction.

This packages `CompletedDiagram.equivalent_iff_transport_eq` and
`CompletedDiagram.equivalent_reconstruct_transport`, following the classification in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §3.
Coefficient maps descend using their existing transport formula; they need not be
injective or surjective.
-/

public section

noncomputable section

universe u

namespace Mei

open Mei.Convex

section General

variable {N V R : Type*} {L L' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (s : KSSpace h) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A consistent completed KS diagram, including its sequence of finite complexes. -/
structure ConsistentDiagram where
  /-- The finite complex at each cutoff. -/
  complex : ℕ → FinitePolyhedralComplex h
  /-- The completed diagram on these complexes. -/
  diagram : CompletedDiagram s d ℒ complex
  /-- Path products depend only on their endpoints at every cutoff. -/
  consistent : diagram.Consistent

namespace ConsistentDiagram

variable {s d ℒ}

/-- Transport from the positive degree point to the negative one. -/
def chamberTransport (D : ConsistentDiagram s d ℒ) : d.completedBCHGroup ℒ :=
  D.diagram.transport D.consistent D.diagram.degreePoint D.diagram.negDegreePoint

/-- The bundled chamber transport is the completed diagram's actual endpoint transport. -/
theorem chamberTransport_def (D : ConsistentDiagram s d ℒ) :
    D.chamberTransport =
      D.diagram.transport D.consistent D.diagram.degreePoint D.diagram.negDegreePoint := (rfl)

/-- Finite common path products agree exactly when chamber transports agree. -/
theorem equivalent_iff_chamberTransport_eq (D E : ConsistentDiagram s d ℒ) :
    D.diagram.Equivalent E.diagram ↔ D.chamberTransport = E.chamberTransport :=
  D.diagram.equivalent_iff_transport_eq E.diagram D.consistent E.consistent

/-- The relation identifying diagrams with equal finite common path products. -/
def setoid : Setoid (ConsistentDiagram s d ℒ) where
  r D E := D.diagram.Equivalent E.diagram
  iseqv :=
    ⟨fun D => (D.equivalent_iff_chamberTransport_eq D).mpr rfl,
      fun {D E} hDE => (E.equivalent_iff_chamberTransport_eq D).mpr
        ((D.equivalent_iff_chamberTransport_eq E).mp hDE).symm,
      fun {D E F} hDE hEF => (D.equivalent_iff_chamberTransport_eq F).mpr
        (((D.equivalent_iff_chamberTransport_eq E).mp hDE).trans
          ((E.equivalent_iff_chamberTransport_eq F).mp hEF))⟩

/-- Consistent completed diagrams modulo equality of finite common path products. -/
def Class : Type _ := Quotient (setoid (s := s) (d := d) (ℒ := ℒ))

/-- The equivalence class of a consistent completed diagram. -/
def toClass (D : ConsistentDiagram s d ℒ) : Class (s := s) (d := d) (ℒ := ℒ) :=
  Quotient.mk _ D

/-- Equality of classes is precisely the original orderwise diagram equivalence. -/
@[simp]
theorem toClass_eq_iff (D E : ConsistentDiagram s d ℒ) :
    D.toClass = E.toClass ↔ D.diagram.Equivalent E.diagram :=
  Quotient.eq

namespace Class

/-- Every diagram class has a consistent representative. -/
@[elab_as_elim]
theorem inductionOn {p : Class (s := s) (d := d) (ℒ := ℒ) → Prop}
    (x : Class (s := s) (d := d) (ℒ := ℒ))
    (hp : ∀ D : ConsistentDiagram s d ℒ, p D.toClass) : p x :=
  Quotient.inductionOn x hp

/-- The chamber transport of a class, independent of its representative. -/
def chamberTransport : Class (s := s) (d := d) (ℒ := ℒ) → d.completedBCHGroup ℒ :=
  Quotient.lift ConsistentDiagram.chamberTransport
    (fun D E hDE => (D.equivalent_iff_chamberTransport_eq E).mp hDE)

/-- The transport of the class of a diagram is its actual chamber transport. -/
@[simp]
theorem chamberTransport_toClass (D : ConsistentDiagram s d ℒ) :
    D.toClass.chamberTransport = D.chamberTransport := (rfl)

/-- A consistent diagram class is determined by its chamber transport. -/
theorem chamberTransport_injective : Function.Injective
    (chamberTransport (s := s) (d := d) (ℒ := ℒ)) := by
  intro x y
  induction x using inductionOn with | _ D =>
    induction y using inductionOn with | _ E =>
      exact fun he => (toClass_eq_iff D E).mpr
        ((D.equivalent_iff_chamberTransport_eq E).mpr he)

variable {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]

/-- Change Lie coefficients in a diagram class. -/
def map (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    Class (s := s) (d := d) (ℒ := ℒ) → Class (s := s) (d := d) (ℒ := ℳ) :=
  Quotient.lift (fun D : ConsistentDiagram s d ℒ =>
    (⟨D.complex, D.diagram.mapDiagram f, D.consistent.mapDiagram f⟩ :
      ConsistentDiagram s d ℳ).toClass) (by
    intro D E hDE
    apply (toClass_eq_iff _ _).mpr
    apply (equivalent_iff_chamberTransport_eq _ _).mpr
    simp only [ConsistentDiagram.chamberTransport, CompletedDiagram.degreePoint_mapDiagram,
      CompletedDiagram.negDegreePoint_mapDiagram]
    rw [D.diagram.transport_mapDiagram D.consistent f,
      E.diagram.transport_mapDiagram E.consistent f]
    exact congrArg f.completedMap ((D.equivalent_iff_chamberTransport_eq E).mp hDE))

/-- On a representative, the class map is represented by the actual coefficient map. -/
@[simp]
theorem map_toClass (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (D : ConsistentDiagram s d ℒ) :
    map f D.toClass =
      (⟨D.complex, D.diagram.mapDiagram f, D.consistent.mapDiagram f⟩ :
        ConsistentDiagram s d ℳ).toClass := (rfl)

/-- Coefficient change on classes is computed by the completed Lie map. -/
@[simp]
theorem chamberTransport_map (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (x : Class (s := s) (d := d) (ℒ := ℒ)) :
    (map f x).chamberTransport = f.completedMap x.chamberTransport := by
  induction x using inductionOn with | _ D =>
    rw [map_toClass, chamberTransport_toClass, chamberTransport_toClass]
    simp only [ConsistentDiagram.chamberTransport, CompletedDiagram.degreePoint_mapDiagram,
      CompletedDiagram.negDegreePoint_mapDiagram]
    exact D.diagram.transport_mapDiagram D.consistent f _ _

/-- An injective degree-preserving coefficient map embeds consistent diagram classes. -/
theorem map_injective (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hf : Function.Injective f) : Function.Injective (map (s := s) f) := by
  intro x y hxy
  apply chamberTransport_injective
  apply f.completedMap_injective hf
  simpa only [chamberTransport_map] using congrArg chamberTransport hxy

/-- The identity coefficient map fixes every consistent diagram class. -/
@[simp]
theorem map_id (x : Class (s := s) (d := d) (ℒ := ℒ)) :
    map (GradedLieHom.id ℒ) x = x := by
  apply chamberTransport_injective
  simp

variable {L'' : Type u} [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L'']
  [IsScalarTower ℚ R L''] {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℋ] [IsPositiveGrading d ℋ]

/-- Coefficient maps compose on classes whenever their underlying Lie maps compose. -/
theorem map_comp (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ)
    (gf : GradedLieHom (PositiveDegreeMap.id d) ℒ ℋ)
    (hgf : gf.toLieHom = g.toLieHom.comp f.toLieHom)
    (x : Class (s := s) (d := d) (ℒ := ℒ)) :
    map gf x = map g (map f x) := by
  apply chamberTransport_injective
  simp only [chamberTransport_map]
  have he := GradedLieHom.completedMap_eq_of_toLieHom_eq gf (g.comp f)
    (hgf.trans (GradedLieHom.toLieHom_comp g f).symm)
  rw [he, GradedLieHom.completedMap_comp, MonoidHom.comp_apply]

end Class

variable {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]

/-- An injective coefficient map reflects equivalence of consistent diagrams. -/
theorem mapDiagram_equivalent_iff (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hf : Function.Injective f) (D E : ConsistentDiagram s d ℒ) :
    (D.diagram.mapDiagram f).Equivalent (E.diagram.mapDiagram f) ↔
      D.diagram.Equivalent E.diagram := by
  constructor
  · intro h
    apply (toClass_eq_iff D E).mp
    apply Class.map_injective f hf
    simpa only [Class.map_toClass] using
      (toClass_eq_iff ⟨D.complex, D.diagram.mapDiagram f, D.consistent.mapDiagram f⟩
        ⟨E.complex, E.diagram.mapDiagram f, E.consistent.mapDiagram f⟩).mpr h
  · intro h
    apply (toClass_eq_iff ⟨D.complex, D.diagram.mapDiagram f, D.consistent.mapDiagram f⟩
      ⟨E.complex, E.diagram.mapDiagram f, E.consistent.mapDiagram f⟩).mp
    simpa only [← Class.map_toClass] using
      congrArg (Class.map f) ((toClass_eq_iff D E).mpr h)

end ConsistentDiagram

end General

namespace PositiveDegrees

variable {N V R : Type*} {L : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  {i : N →+ V} (d : PositiveDegrees N)
  (h : TauCeti.Toric.IsIntegralLattice i) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Consistent KS diagram classes are canonically the completed BCH group;
the inverse is the class of the middle-factor reconstruction. -/
def reconstructionEquiv :
    ConsistentDiagram.Class (s := KSSpace.continuousDual h) (d := d) (ℒ := ℒ) ≃
      d.completedBCHGroup ℒ where
  toFun := ConsistentDiagram.Class.chamberTransport
  invFun g := (⟨_, d.reconstruct h ℒ g, d.consistent_reconstruct h ℒ g⟩ :
    ConsistentDiagram (KSSpace.continuousDual h) d ℒ).toClass
  left_inv x := by
    apply ConsistentDiagram.Class.chamberTransport_injective
    exact d.transport_reconstruct h ℒ x.chamberTransport
  right_inv := d.transport_reconstruct h ℒ

/-- Reconstruction identifies a class with its chamber transport. -/
@[simp]
theorem reconstructionEquiv_apply
    (x : ConsistentDiagram.Class (s := KSSpace.continuousDual h) (d := d) (ℒ := ℒ)) :
    d.reconstructionEquiv h ℒ x = x.chamberTransport := (rfl)

/-- The inverse classification map is represented by the reconstructed diagram. -/
theorem reconstructionEquiv_symm_apply (g : d.completedBCHGroup ℒ) :
    (d.reconstructionEquiv h ℒ).symm g =
      (⟨_, d.reconstruct h ℒ g, d.consistent_reconstruct h ℒ g⟩ :
        ConsistentDiagram (KSSpace.continuousDual h) d ℒ).toClass := (rfl)

/-- Classification respects every finite-order path computing chamber transport. -/
theorem projection_reconstructionEquiv_toClass
    (D : ConsistentDiagram (KSSpace.continuousDual h) d ℒ) (k : ℕ)
    (p : AdmissiblePLPath (CommonWallComplement.projection k D.diagram.degreePoint)
      (CommonWallComplement.projection k D.diagram.negDegreePoint)) :
    CompletedGroup.projection k (d.reconstructionEquiv h ℒ D.toClass) =
      (D.diagram.diagram k).toFiniteWallDiagram.pathProduct p :=
  D.diagram.projection_transport D.consistent k p

end PositiveDegrees

namespace ConsistentDiagram.Class

variable {N V R : Type*} {L : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  {i : N →+ V} (d : PositiveDegrees N)
  (h : TauCeti.Toric.IsIntegralLattice i) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A surjective coefficient map is surjective on consistent diagram classes. -/
theorem map_surjective {L' : Type u}
    [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
    {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (hf : Function.Surjective f) :
    Function.Surjective (ConsistentDiagram.Class.map (s := KSSpace.continuousDual h) f) := by
  intro y
  obtain ⟨x, hx⟩ := f.completedMap_surjective hf (d.reconstructionEquiv h ℳ y)
  refine ⟨(d.reconstructionEquiv h ℒ).symm x, ?_⟩
  apply (d.reconstructionEquiv h ℳ).injective
  rw [PositiveDegrees.reconstructionEquiv_apply, chamberTransport_map,
    ← PositiveDegrees.reconstructionEquiv_apply, Equiv.apply_symm_apply]
  exact hx


end ConsistentDiagram.Class
end Mei
