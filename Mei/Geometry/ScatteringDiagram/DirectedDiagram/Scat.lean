/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Class
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Presentation
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Limit

/-!
# The outgoing scattering class

A finitely active full-hyperplane input determines a unique class of outgoing
completions, denoted `DirectedDiagram.Scat`. Its finite-order projection depends
only on the corresponding finite-order class of the input. Fixed-degree
wall-space morphisms commute with this construction, including maps that kill
initial labels or correction labels.

This packages `DirectedDiagram.exists_outgoingCompletion`,
`DirectedDiagram.outgoingCompletion_unique` and
`DirectedDiagram.outgoingCompletion_levelEquivalent_of_initial_levelEquivalent`.
The mathematical construction is Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Theorem 2.6. The chosen representative has
countably many corrections; only its class enters the public construction.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v w

variable {Γ Λ R V : Type*} {L L' : Type v} {ι κ : Type u}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [Module.Free ℤ Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  (D : DirectedDiagram (d := d) h H ι)
  (hfull : ∀ j, ∃ a : ℝ,
    (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})

include hfull in
private theorem exists_scat_class :
    ∃ c : Class.{u} (d := d) (h := h) (H := H),
      ∃ (η : Type) (E : DirectedDiagram (d := d) h H (ι ⊕ η)),
        IsOutgoingCompletion D.wall E ∧ c = E.toClass := by
  obtain ⟨η, _, E, hE, _⟩ := D.exists_outgoingCompletion hfull
  exact ⟨E.toClass, η, E, hE, rfl⟩

/-- The equivalence class of an outgoing completion of a full-hyperplane input.
The index universe is the input's universe; the additional walls can be countable. -/
def Scat : Class.{u} (d := d) (h := h) (H := H) :=
  (D.exists_scat_class hfull).choose

/-- The scattering class has a representative that is an outgoing completion of the input. -/
theorem scat_spec :
    ∃ (η : Type) (E : DirectedDiagram (d := d) h H (ι ⊕ η)),
      IsOutgoingCompletion D.wall E ∧ D.Scat hfull = E.toClass :=
  (D.exists_scat_class hfull).choose_spec

/-- Every outgoing completion represents the scattering class. -/
theorem scat_eq_toClass {ι : Type (max u w)}
    (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    {η : Type w} {E : DirectedDiagram (d := d) h H (ι ⊕ η)}
    (hE : IsOutgoingCompletion D.wall E) : D.Scat hfull = E.toClass := by
  obtain ⟨η, F, hF, hc⟩ := D.scat_spec hfull
  exact hc.trans ((toClass_eq_iff F E).mpr (outgoingCompletion_unique hF hE))

variable {D}

/-- The order-`k` scattering class depends only on the order-`k` input class. -/
theorem projection_scat_eq_of_levelEquivalent
    {E : DirectedDiagram (d := d) h H κ}
    (hfullE : ∀ j, ∃ a : ℝ,
      (E.wall j).support = {x | h.realCharacter (E.wall j).normal x = a})
    {k : ℕ} (hDE : D.LevelEquivalent E k) :
    (D.Scat hfull).projection k = (E.Scat hfullE).projection k := by
  obtain ⟨η, F, hF, hcF⟩ := D.scat_spec hfull
  obtain ⟨θ, G, hG, hcG⟩ := E.scat_spec hfullE
  rw [hcF, hcG, Class.projection_toClass, Class.projection_toClass]
  exact (toLevelClass_eq_iff F G k).mpr
    (outgoingCompletion_levelEquivalent_of_initial_levelEquivalent hDE
      hF.wall_inl hG.wall_inl
      ((consistent_iff F).mp hF.consistent k) ((consistent_iff G).mp hG.consistent k)
      (fun j _ => hF.outgoing_inr j) (fun j _ => hG.outgoing_inr j))

/-- Equivalent full-hyperplane presentations give the same scattering class. -/
theorem scat_eq_of_equivalent {E : DirectedDiagram (d := d) h H κ}
    (hfullE : ∀ j, ∃ a : ℝ,
      (E.wall j).support = {x | h.realCharacter (E.wall j).normal x = a})
    (hDE : D.Equivalent E) : D.Scat hfull = E.Scat hfullE := by
  apply Class.ext
  intro k
  exact projection_scat_eq_of_levelEquivalent hfull hfullE ((equivalent_iff _ _).mp hDE k)

variable (D)

/-- Changing Lie coefficients commutes with the outgoing scattering class. -/
theorem map_scat (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m) :
    Class.map f hf (D.Scat hfull) = (D.map f hf).Scat (by
      simpa only [map_wall, DirectedWall.map_support, DirectedWall.map_normal] using hfull) := by
  obtain ⟨η, E, hE, hc⟩ := D.scat_spec hfull
  obtain ⟨θ, F, hF, hcF⟩ := (D.map f hf).scat_spec (by
    simpa only [map_wall, DirectedWall.map_support, DirectedWall.map_normal] using hfull)
  rw [hc, Class.map_toClass, hcF]
  have hinput : (D.map f hf).wall = fun j => (D.wall j).map f hf :=
    funext (map_wall D f hf)
  rw [hinput] at hF
  exact (toClass_eq_iff _ _).mpr (outgoingCompletion_unique (hE.map f hf) hF)

end Mei.DirectedDiagram
