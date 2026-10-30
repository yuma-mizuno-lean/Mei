/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence.Basic

/-!
# Truncation of transport on adapted complexes

At two cutoffs, paths with the same ambient vertices in the respective adapted
complexes have compatible path products. The coorientations may be chosen
independently. Consistency is unnecessary: the comparison uses the same geometric
path, including the walls whose labels become identity at the lower cutoff.

We combine `levelPathProduct_eq_adaptedDiagram`, `truncation_levelPathProduct`,
and `levelPathProduct_eq_of_vertices_eq`. This is the transport comparison needed
to lower the coefficient order of sections on the adapted regular loci.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Lowering the cutoff projects the adapted transport along the same ambient
polygonal path, with arbitrary coorientations at either cutoff. -/
theorem truncation_pathProduct_adaptedDiagram {k l : ℕ} (hkl : k ≤ l)
    (νk : (D.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
    (hνk : ∀ Q, (νk Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    (νl : (D.adaptedComplex l).walls → V →ₗ[ℝ] ℝ)
    (hνl : ∀ Q, (νl Q).ker = (affineSpan ℝ (Q : Set V)).direction)
    {x y : WallComplement (fun Q : (D.adaptedComplex l).walls => (Q : Set V))}
    {x' y' : WallComplement (fun Q : (D.adaptedComplex k).walls => (Q : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    (d.truncationMap ℒ hkl).bchGroupMap ((D.adaptedDiagram l νl hνl).pathProduct p) =
      (D.adaptedDiagram k νk hνk).pathProduct q := by
  rw [← D.levelPathProduct_eq_adaptedDiagram νl hνl p,
    D.truncation_levelPathProduct hkl,
    ← D.levelPathProduct_eq_adaptedDiagram νk hνk q]
  apply D.levelPathProduct_eq_of_vertices_eq
  simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    WallComplement.restrictPrefunctor_obj_val, D.adaptedPathPrefunctor_obj_val] using hpq

end Mei.DirectedDiagram
