/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.WallSpace.Truncation

/-!
# Lie truncation of directed scattering classes

Mapping labels to the Lie quotient at order `k` identifies exactly those diagrams
whose path products agree at that order. Consequently finite-order diagram classes
embed into completed diagram classes for the truncated Lie algebra, and outgoing
scattering commutes with this embedding.

The cutoff comparison uses the injectivity of quotient transitions once the degree
ideal vanishes. The label comparison uses `GradedLieHom.truncation` and its
finite quotient map; wall-space preservation uses the actual quotient images
`DirectedWallSpaces.truncated`. Outgoing completions are
transported by `DirectedDiagram.map_scat`, the coefficient naturality of Mandel's
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Theorem 2.6, arXiv:1503.06183v5.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R L V : Type*} {ι κ : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ} {ℒ : Γ → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- Quotient labels agree at every order exactly when the original diagrams agree
at the retained cutoff. This also reflects equivalence for inconsistent diagrams. -/
@[simp]
theorem equivalent_map_truncation_iff
    (D : DirectedDiagram (d := d) h H ι) (E : DirectedDiagram (d := d) h H κ) (k : ℕ) :
    (D.map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k)).Equivalent
        (E.map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k)) ↔
      D.LevelEquivalent E k := by
  rw [equivalent_iff_levelEquivalent_of_degreeIdeal_eq_bot _ _
    (d.degreeIdeal_truncatedGrading_eq_bot ℒ le_rfl)]
  apply levelEquivalent_map_iff_of_injective
  rw [GradedLieHom.truncatedMap_truncation, ← LieHom.ker_eq_bot, LieIdeal.mkQ_ker]
  exact d.degreeIdeal_truncatedGrading_eq_bot ℒ le_rfl

/-- Interpret a finite-order class as a completed class with coefficients in the
finite Lie quotient. The result depends only on the given finite-order class. -/
def LevelClass.truncate (k : ℕ) :
    LevelClass.{u} (d := d) (h := h) (H := H) k →
      Class.{u} (d := d) (h := h) (H := H.truncated d k) :=
  LevelClass.lift k
    (fun D => (D.map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k)).toClass)
    (fun D E hDE => (toClass_eq_iff _ _).mpr
      ((equivalent_map_truncation_iff D E k).mpr hDE))

/-- On a representative, finite-class truncation maps every label by the Lie quotient. -/
@[simp]
theorem LevelClass.truncate_toLevelClass (D : DirectedDiagram (d := d) h H ι) (k : ℕ) :
    LevelClass.truncate k (D.toLevelClass k) =
      (D.map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k)).toClass := by
  rw [truncate, lift_toLevelClass]

/-- Passing to the quotient Lie algebra loses no information from a finite-order class. -/
theorem LevelClass.truncate_injective (k : ℕ) :
    Function.Injective (truncate (d := d) (h := h) (H := H) k) := by
  intro x y
  induction x using LevelClass.inductionOn with | _ D =>
    induction y using LevelClass.inductionOn with | _ E =>
      intro he
      rw [truncate_toLevelClass, truncate_toLevelClass, toClass_eq_iff,
        equivalent_map_truncation_iff] at he
      exact (toLevelClass_eq_iff D E k).mpr he

/-- Equality after finite-class truncation is exactly equality at the cutoff. -/
@[simp]
theorem LevelClass.truncate_inj (k : ℕ)
    {x y : LevelClass.{u} (d := d) (h := h) (H := H) k} :
    truncate k x = truncate k y ↔ x = y :=
  (truncate_injective k).eq_iff

/-- Mapping a completed class to a finite Lie quotient factors through precisely its
finite-order projection. -/
theorem Class.map_truncation (c : Class.{u} (d := d) (h := h) (H := H)) (k : ℕ) :
    map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k) c =
      LevelClass.truncate k (c.projection k) := by
  induction c using Class.inductionOn with | _ D =>
    simp only [map_toClass, projection_toClass, LevelClass.truncate_toLevelClass]

variable [Module.Free ℤ Γ]

/-- The order-`k` outgoing scattering class, interpreted in the quotient Lie algebra,
is the outgoing scattering class of the truncated input. -/
theorem truncate_projection_scat (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a}) (k : ℕ) :
    LevelClass.truncate k ((D.Scat hfull).projection k) =
      (D.map (GradedLieHom.truncation d ℒ k) (H.truncation_mem_wall d k)).Scat (by
        simpa only [map_wall, DirectedWall.map_support, DirectedWall.map_normal] using hfull) := by
  rw [← Class.map_truncation]
  exact D.map_scat hfull _ _

end Mei.DirectedDiagram
