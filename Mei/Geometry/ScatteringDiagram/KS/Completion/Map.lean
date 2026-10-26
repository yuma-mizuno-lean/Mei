/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Map

/-!
# Change of coefficients in completed KS diagrams

A degree-preserving Lie homomorphism maps each finite level using `KSComplex.map`.
The quotient-transition naturality square makes these levels compatible, even for
nonstabilizing sequences of complexes and noninjective coefficient maps. Identity
and composition commute with this construction. Completed geometric path products,
consistency and endpoint transport are preserved by `GradedLieHom.completedMap`.

This uses the finite coefficient maps in `Mei.Geometry.ScatteringDiagram.KS.Map`
and the compatible-family construction of `CompletedDiagram`.
-/

public section

noncomputable section

universe u

namespace Mei

open Set Mei.Convex

variable {N V R : Type*} {L L' L'' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]

namespace CompletedDiagram

variable {C : ℕ → FinitePolyhedralComplex h}

/-- Change the Lie coefficients at every order of a completed KS diagram. -/
def mapDiagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : CompletedDiagram s d ℳ C where
  diagram k := (D.diagram k).map f
  compatible k {_ _ _ _} p q hpq := by
    simp only [KSComplex.pathProduct_map]
    have hc := D.compatible k p q hpq
    have hn := DFunLike.congr_fun
      (congrArg LieHom.bchGroupMap
        (f.truncationMap_comp_truncatedMap_of_le (Nat.le_succ k)
          (Nat.le_succ k) (by simp) (by simp)))
      ((D.diagram (k + 1)).toFiniteWallDiagram.pathProduct q)
    simpa only [LieHom.bchGroupMap_comp, MonoidHom.comp_apply, hc] using hn

/-- The finite levels of coefficient change are the existing finite diagram maps. -/
@[simp]
theorem mapDiagram_diagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (k : ℕ) :
    (D.mapDiagram f).diagram k = (D.diagram k).map f := (rfl)

/-- The identity coefficient map leaves a completed diagram unchanged. -/
@[simp]
theorem mapDiagram_id (D : CompletedDiagram s d ℒ C) :
    D.mapDiagram (GradedLieHom.id ℒ) = D := by
  apply CompletedDiagram.ext
  funext k
  simp

/-- Successive maps of completed diagrams compose as equalities. -/
@[simp]
theorem mapDiagram_comp (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.mapDiagram f).mapDiagram g =
      D.mapDiagram (by simpa only [PositiveDegreeMap.id_comp] using g.comp f) := by
  apply CompletedDiagram.ext
  funext k
  simp only [mapDiagram_diagram]
  rw [KSComplex.map_map]
  congr 1
  ext x
  simp [GradedLieHom.comp_apply, ← GradedLieHom.coe_toLieHom]

/-- The complete product is natural for the completed Lie coefficient map. -/
@[simp]
theorem pathProduct_mapDiagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    {x y : Point C} (p : Quiver.Path x y) :
    (D.mapDiagram f).pathProduct p = f.completedMap (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  rw [f.projection_completedMap_of_le k (a := k) (by simp)]
  simp only [projection_pathProduct, mapDiagram_diagram, KSComplex.pathProduct_map]
  -- The tower projections use the concrete BCH group operations.
  rfl

/-- A map of Lie coefficients preserves consistency at all orders. -/
theorem Consistent.mapDiagram {D : CompletedDiagram s d ℒ C} (hD : D.Consistent)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : (D.mapDiagram f).Consistent := by
  apply (consistent_iff _).mpr
  intro k
  exact (D.diagram k).consistent_map f ((consistent_iff _).mp hD k)

/-- Endpoint transport commutes with the completed coefficient map. -/
theorem transport_mapDiagram (D : CompletedDiagram s d ℒ C) (hD : D.Consistent)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (x y : Point C) :
    (D.mapDiagram f).transport (hD.mapDiagram f) x y =
      f.completedMap (D.transport hD x y) := by
  obtain ⟨p⟩ := exists_path x y
  rw [transport_eq_pathProduct _ (hD.mapDiagram f) p,
    D.transport_eq_pathProduct hD p, pathProduct_mapDiagram]

end CompletedDiagram

end Mei
