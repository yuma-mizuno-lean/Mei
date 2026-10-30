/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Presentation
public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Map
public import Mei.Geometry.ScatteringDiagram.KS.Completion.Map

/-!
# Coefficient naturality of the KS diagram of a presentation

Mapping the labels of an indexed presentation before conversion to KS complexes gives
the same path products as mapping the resulting KS complexes. The complexes themselves
can differ: the image presentation discards inactive supports before subdivision, whereas
mapping a KS complex retains its geometry. The resulting completed diagrams are equivalent.

The argument combines `IndexedWallPresentation.pathProduct_toKSComplex` with
`IndexedWallPresentation.levelPathProduct_mapPathPrefunctor` and `KSComplex.pathProduct_map`.
This is the coefficient compatibility of the abelian-ray description in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.IndexedWallPresentation

universe u

variable {N V R : Type*} {L L' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [Module.Free ℤ N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  [IsAbelianRays d ℒ] [IsAbelianRays d ℳ]
  {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Converting a mapped presentation to a KS complex maps the original test product,
even when the two subdivisions differ because some labels vanish. -/
theorem pathProduct_toKSComplex_map (k : ℕ)
    {x y : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V))}
    {x' y' : WallComplement (fun Q : ((D.map f).levelComplex k).walls => (Q : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    ((D.map f).toKSComplex k).toFiniteWallDiagram.pathProduct q =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap
        ((D.toKSComplex k).toFiniteWallDiagram.pathProduct p) := by
  let r := (D.pathPrefunctor k).mapPath p
  let r' := (D.mapPathPrefunctor f k).mapPath r
  have hv : q.vertices.map WallComplement.val = r'.vertices.map WallComplement.val := by
    rw [D.vertices_mapPathPrefunctor f k r]
    simp only [r, Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      pathPrefunctor_obj_val]
    exact hpq.symm
  rw [(D.map f).pathProduct_toKSComplex k q r' hv,
    D.levelPathProduct_mapPathPrefunctor f k r,
    D.pathProduct_toKSComplex_eq_levelPathProduct_mapPath k p]

/-- Conversion of presentations to completed KS diagrams commutes with coefficient change
up to equivalence. No consistency or injectivity hypothesis is needed. -/
theorem toCompletedDiagram_map_equivalent :
    (D.map f).toCompletedDiagram.Equivalent (D.toCompletedDiagram.mapDiagram f) := by
  rw [CompletedDiagram.equivalent_iff]
  intro k x y x' y' p q hpq
  simp only [toCompletedDiagram_diagram, CompletedDiagram.mapDiagram_diagram,
    KSComplex.pathProduct_map]
  exact D.pathProduct_toKSComplex_map f k q p hpq.symm

end Mei.IndexedWallPresentation
