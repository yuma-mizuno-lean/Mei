/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Cylinder
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence.Basic

/-!
# Equivalence through the charge-zero cylinders of a module probe

Equivalent base diagrams have equivalent charge-zero cylinders in a module probe,
at each finite cutoff and in the completion. The two wall families may have unrelated
index types.

Common admissible cylinder paths project to common admissible base paths, and the
products are identified by the injective charge-zero inclusion. The comparison uses
`DirectedDiagram.levelEquivalent_of_levelPathProduct_map` with the existing
`ModuleProbe.levelPathProduct_cylinderDiagram` formula.
-/

public section
noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  {D : DirectedDiagram (d := d) h H ι} {D' : DirectedDiagram (d := d) h H κ}

/-- Equivalent base diagrams have equivalent charge-zero probe cylinders at the same cutoff. -/
theorem _root_.Mei.DirectedDiagram.LevelEquivalent.cylinderDiagram {k : ℕ}
    (hDD' : D.LevelEquivalent D' k) :
    (cylinderDiagram d ℳ p ℒ H h h' D).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' D') k :=
  DirectedDiagram.levelEquivalent_of_levelPathProduct_map _
    (cylinderPathProjection d ℳ p ℒ H h h' D k) (cylinderPathProjection d ℳ p ℒ H h h' D' k)
    (fun p => by rw [levelPathProduct_cylinderDiagram])
    (fun p => by rw [levelPathProduct_cylinderDiagram])
    (fun p q hpq => by
      simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
        cylinderPathProjection_obj_val] using congrArg (List.map Prod.fst) hpq) hDD'

/-- Equivalent base diagrams have equivalent charge-zero probe cylinders. -/
theorem _root_.Mei.DirectedDiagram.Equivalent.cylinderDiagram (hDD' : D.Equivalent D') :
    (cylinderDiagram d ℳ p ℒ H h h' D).Equivalent (cylinderDiagram d ℳ p ℒ H h h' D') :=
  (DirectedDiagram.equivalent_iff _ _).mpr fun k =>
    ((DirectedDiagram.equivalent_iff _ _).mp hDD' k).cylinderDiagram d ℳ p ℒ H h h'

end Mei.ModuleProbe
