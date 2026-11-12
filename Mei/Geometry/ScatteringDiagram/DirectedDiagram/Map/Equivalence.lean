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

These are the special case `DirectedWall.Pushforward.ofFixedDegree` of
`DirectedDiagram.LevelEquivalent.pushforward`, allowing the active supports to disappear.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

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
  rw [← pushforward_ofFixedDegree, ← pushforward_ofFixedDegree]
  exact hDE.pushforward (by simp)

/-- A coefficient map injective at the cutoff preserves and reflects finite-order
equivalence, including for inconsistent diagrams. -/
theorem levelEquivalent_map_iff_of_injective (k : ℕ)
    (hinj : Function.Injective (f.truncatedMap k (a := k) (by simp))) :
    (D.map f hf).LevelEquivalent (E.map f hf) k ↔ D.LevelEquivalent E k := by
  refine ⟨?_, fun hDE => hDE.map f hf⟩
  rw [← pushforward_ofFixedDegree, ← pushforward_ofFixedDegree, levelEquivalent_def,
    levelEquivalent_def]
  intro hDE x y x' y' p q hpq
  apply LieHom.bchGroupMap_injective hinj
  rw [← DirectedWall.Pushforward.ofFixedDegree_lieHom_truncatedMap (h := h) f hf k (by simp)]
  refine (D.levelPathProduct_pushforward (.ofFixedDegree f hf) k (by simp) p).symm.trans
    (Eq.trans ?_ (E.levelPathProduct_pushforward (.ofFixedDegree f hf) k (by simp) q))
  apply hDE
  simpa [Prefunctor.vertices_mapPath, Function.comp_def] using hpq

/-- Equivalent directed presentations remain equivalent after changing coefficients,
even if they have different index types and different active supports. -/
theorem Equivalent.map (hDE : D.Equivalent E) :
    (D.map f hf).Equivalent (E.map f hf) := by
  rw [← pushforward_ofFixedDegree, ← pushforward_ofFixedDegree]
  exact hDE.pushforward

end Mei.DirectedDiagram
