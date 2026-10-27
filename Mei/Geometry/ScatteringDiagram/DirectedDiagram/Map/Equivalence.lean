/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Basic

/-!
# Coefficient maps on directed equivalence classes

Fixed-degree coefficient maps preserve finite-order and all-order equivalence of
directed diagrams. In particular, changing coefficients of a completion is
independent of its wall presentation. Labels may vanish under the map, so a path
admissible for the image need not be admissible for the original diagram.

The comparison combines `DirectedDiagram.exists_common_levelPathProduct_eq` with
`DirectedDiagram.levelPathProduct_mapPathPrefunctor`. It follows the coefficient
naturality of `CompletedDiagram.Equivalent.mapDiagram`, while allowing the active
supports to disappear.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R V ι κ : Type*} {L L' : Type u}
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
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H κ}
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hf : ∀ n m, ∀ x ∈ H.wall n m, f x ∈ H'.wall n m)

/-- Coefficient maps preserve equivalence at each cutoff, including paths through
supports of labels that the map kills. Neither diagram need be consistent. -/
theorem LevelEquivalent.map {k : ℕ} (hDE : D.LevelEquivalent E k) :
    (D.map f hf).LevelEquivalent (E.map f hf) k := by
  apply (levelEquivalent_def _ _ _).mpr
  intro x y x' y' p q hpq
  let W : Unit → D.active k ⊕ E.active k → Set V := fun _ =>
    Sum.elim (fun j => (D.wall j).support) (fun j => (E.wall j).support)
  have hpoly : ∀ j a, TauCeti.IsConvexPolyhedron (W j a) := by
    rintro _ (a | a)
    · exact (D.wall a).isConvexPolyhedron
    · exact (E.wall a).isConvexPolyhedron
  have hdim : ∀ j a, Module.finrank ℝ (affineSpan ℝ (W j a)).direction + 1 =
      Module.finrank ℝ V := by
    rintro _ (a | a)
    · exact (D.wall a).finrank_direction_add_one
    · exact (E.wall a).finrank_direction_add_one
  obtain ⟨a, b, r, hP, hQ⟩ := (D.map f hf).exists_common_levelPathProduct_eq
    (E.map f hf) k k hpoly hdim p q hpq
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  let pD : WallComplement (W ()) ⥤q
      WallComplement (fun j : D.active k => (D.wall j).support) :=
    restrictPrefunctor (W ()) Sum.inl
  let pE : WallComplement (W ()) ⥤q
      WallComplement (fun j : E.active k => (E.wall j).support) :=
    restrictPrefunctor (W ()) Sum.inr
  let rD := pD.mapPath r₀
  let rE := pE.mapPath r₀
  have hvD : rD.vertices.map WallComplement.val =
      r.vertices.map CommonWallComplement.val :=
    (vertices_restrictPrefunctor (W ()) Sum.inl r₀).trans
      (CommonWallComplement.vertices_projection () r)
  have hvE : rE.vertices.map WallComplement.val =
      r.vertices.map CommonWallComplement.val :=
    (vertices_restrictPrefunctor (W ()) Sum.inr r₀).trans
      (CommonWallComplement.vertices_projection () r)
  have hvMapD : ((D.mapPathPrefunctor f hf k).mapPath rD).vertices.map
      WallComplement.val = r.vertices.map CommonWallComplement.val := by
    simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      mapPathPrefunctor_obj_val] using hvD
  have hvMapE : ((E.mapPathPrefunctor f hf k).mapPath rE).vertices.map
      WallComplement.val = r.vertices.map CommonWallComplement.val := by
    simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      mapPathPrefunctor_obj_val] using hvE
  rw [← hP _ hvMapD, ← hQ _ hvMapE, levelPathProduct_mapPathPrefunctor,
    levelPathProduct_mapPathPrefunctor,
    (levelEquivalent_def _ _ _).mp hDE rD rE (hvD.trans hvE.symm)]

/-- Equivalent directed presentations remain equivalent after changing coefficients,
even if they have different index types and different active supports. -/
theorem Equivalent.map (hDE : D.Equivalent E) :
    (D.map f hf).Equivalent (E.map f hf) := by
  rw [equivalent_iff] at hDE ⊢
  exact fun k => (hDE k).map f hf

end Mei.DirectedDiagram
