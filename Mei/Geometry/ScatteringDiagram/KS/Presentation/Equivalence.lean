/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Presentation
public import Mei.Geometry.ScatteringDiagram.KS.Equivalence
public import Mei.Geometry.Convex.Polyhedron.Path.CommonProduct

/-!
# Equivalence of indexed KS presentations

Indexed abelian-ray presentations are equivalent when their active-wall products
agree on common admissible vertex lists at every cutoff. Conversion to completed
KS diagrams preserves and reflects this relation. In particular, the extra cuts
used to form the finite KS complexes do not lose any test products: each pair of
tests can be perturbed to common paths in those complexes while retaining both
original products. Repeated supports, identity labels and lineality are allowed;
neither presentation is assumed consistent.

The comparison uses `IndexedWallPresentation.pathProduct_toKSComplex` and
`Quiver.Path.exists_common_wallPathProduct_eq`. This is the path-product
equivalence of abelian-ray presentations in Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), compared with
Bridgeland's finite-complex description in *Scattering diagrams, Hall algebras and
stability conditions*, Definition 2.3 (arXiv:1603.00416v4).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.IndexedWallPresentation

variable {N V R L ι κ η : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Module.Free ℤ N] [IsAbelianRays d ℒ]
  (D : IndexedWallPresentation s d ℒ ι) (E : IndexedWallPresentation s d ℒ κ)

/-- Agreement of the active-wall products on every common admissible vertex list
at one cutoff. The indexed wall families may differ. -/
def LevelEquivalent (k : ℕ) : Prop :=
  ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
    ⦃x' y' : WallComplement (fun j : E.active k => (E.wall j).support)⦄
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
    p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
      D.levelPathProduct k p = E.levelPathProduct k q

/-- The finite common-path characterization of presentation equivalence. -/
theorem levelEquivalent_def (k : ℕ) : D.LevelEquivalent E k ↔
    ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
      ⦃x' y' : WallComplement (fun j : E.active k => (E.wall j).support)⦄
      (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
      p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
        D.levelPathProduct k p = E.levelPathProduct k q := Iff.rfl

/-- Two tests in the indexed families can be computed by common paths in their
finite KS complexes. Endpoints may move to avoid the extra cuts, without changing
either product. -/
theorem exists_common_toKSComplex_pathProduct_eq (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : E.active k => (E.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    ∃ (a b : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V)))
      (a' b' : WallComplement (fun Q : (E.levelComplex k).walls => (Q : Set V)))
      (p' : AdmissiblePLPath a b) (q' : AdmissiblePLPath a' b'),
      p'.vertices.map WallComplement.val = q'.vertices.map WallComplement.val ∧
      (D.toKSComplex k).toFiniteWallDiagram.pathProduct p' = D.levelPathProduct k p ∧
      (E.toKSComplex k).toFiniteWallDiagram.pathProduct q' = E.levelPathProduct k q := by
  let := h.finiteDimensional
  let C : Bool → FinitePolyhedralComplex h :=
    fun b => if b then E.levelComplex k else D.levelComplex k
  obtain ⟨a, b, r, hP, hQ⟩ := p.exists_common_wallPathProduct_eq
    (fun j : D.active k => (D.wall j).isConvexPolyhedron.isClosed)
    (fun j => (D.wall j).finrank_direction_add_one)
    (fun j => s.normal (D.wall j).ray.generator)
    (fun j => (D.wall j).direction_support.symm)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)
    (fun j : E.active k => (E.wall j).isConvexPolyhedron.isClosed)
    (fun j => (E.wall j).finrank_direction_add_one)
    (fun j => s.normal (E.wall j).ray.generator)
    (fun j => (E.wall j).direction_support.symm)
    (fun j => CompletedGroup.projection k (E.wall j).label) (E.activeLabels_commute k)
    (A := fun b => fun Q : (C b).walls => (Q : Set V))
    (fun b Q => (C b).isConvexPolyhedron ((C b).mem_cells_of_mem_walls Q.property))
    (fun b Q => (C b).finrank_direction_add_one_of_mem_walls Q.property) q hpq
  -- Fix the endpoint types before elaborating products, so unification does not
  -- unfold the hidden wall inventories of the two finite complexes.
  let aD : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V)) :=
    CommonWallComplement.projection false a
  let bD : WallComplement (fun Q : (D.levelComplex k).walls => (Q : Set V)) :=
    CommonWallComplement.projection false b
  let aE : WallComplement (fun Q : (E.levelComplex k).walls => (Q : Set V)) :=
    CommonWallComplement.projection true a
  let bE : WallComplement (fun Q : (E.levelComplex k).walls => (Q : Set V)) :=
    CommonWallComplement.projection true b
  let p' : AdmissiblePLPath aD bD := (CommonWallComplement.projectionPrefunctor false).mapPath r
  let q' : AdmissiblePLPath aE bE := (CommonWallComplement.projectionPrefunctor true).mapPath r
  have hvP : p'.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    CommonWallComplement.vertices_projection false r
  have hvQ : q'.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    CommonWallComplement.vertices_projection true r
  refine ⟨_, _, _, _, p', q', hvP.trans hvQ.symm, ?_, ?_⟩
  · rw [D.pathProduct_toKSComplex_eq_levelPathProduct_mapPath]
    rw [D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k),
      D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
    apply hP
    simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      pathPrefunctor_obj_val] using hvP
  · rw [E.pathProduct_toKSComplex_eq_levelPathProduct_mapPath]
    rw [E.levelPathProduct_eq_wallPathProduct k _ (E.activeLabels_commute k),
      E.levelPathProduct_eq_wallPathProduct k q (E.activeLabels_commute k)]
    apply hQ
    simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      pathPrefunctor_obj_val] using hvQ

/-- Conversion to finite KS complexes preserves and reflects equivalence at each
cutoff, including tests whose vertices lie on the auxiliary cuts. -/
theorem levelEquivalent_iff_toKSComplex (k : ℕ) : D.LevelEquivalent E k ↔
    (D.toKSComplex k).toFiniteWallDiagram.Equivalent (E.toKSComplex k).toFiniteWallDiagram := by
  rw [levelEquivalent_def, FiniteWallDiagram.equivalent_def]
  constructor
  · intro hDE x y x' y' p q hpq
    rw [D.pathProduct_toKSComplex_eq_levelPathProduct_mapPath,
      E.pathProduct_toKSComplex_eq_levelPathProduct_mapPath]
    apply hDE
    simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
      pathPrefunctor_obj_val] using hpq
  · intro hDE x y x' y' p q hpq
    obtain ⟨_, _, _, _, p', q', hv, hp, hq⟩ :=
      D.exists_common_toKSComplex_pathProduct_eq E k p q hpq
    exact hp.symm.trans ((hDE p' q' hv).trans hq)

/-- Finite-order presentation equivalence is reflexive. -/
theorem LevelEquivalent.refl (k : ℕ) : D.LevelEquivalent D k :=
  (D.levelEquivalent_iff_toKSComplex D k).mpr (FiniteWallDiagram.Equivalent.refl _)

variable {D E} {F : IndexedWallPresentation s d ℒ η}

/-- Finite-order presentation equivalence is symmetric. -/
@[symm]
theorem LevelEquivalent.symm {k : ℕ} (hDE : D.LevelEquivalent E k) :
    E.LevelEquivalent D k :=
  (E.levelEquivalent_iff_toKSComplex D k).mpr
    ((D.levelEquivalent_iff_toKSComplex E k).mp hDE).symm

/-- Finite-order presentation equivalence is transitive, even when the original
vertices lie on active walls of the intermediate presentation. -/
@[trans]
theorem LevelEquivalent.trans {k : ℕ} (hDE : D.LevelEquivalent E k)
    (hEF : E.LevelEquivalent F k) : D.LevelEquivalent F k :=
  (D.levelEquivalent_iff_toKSComplex F k).mpr
    (((D.levelEquivalent_iff_toKSComplex E k).mp hDE).trans
      ((E.levelEquivalent_iff_toKSComplex F k).mp hEF))

variable (D E)

/-- Indexed presentations are equivalent when all finite common path products agree. -/
def Equivalent : Prop := ∀ k, D.LevelEquivalent E k

/-- Presentation equivalence is finite-order equivalence at every cutoff. -/
theorem equivalent_iff : D.Equivalent E ↔ ∀ k, D.LevelEquivalent E k := Iff.rfl

/-- The completed KS construction preserves and reflects the original equivalence
of indexed presentations; its auxiliary subdivisions do not identify extra diagrams. -/
theorem equivalent_iff_toCompletedDiagram : D.Equivalent E ↔
    D.toCompletedDiagram.Equivalent E.toCompletedDiagram := by
  rw [equivalent_iff, CompletedDiagram.equivalent_iff]
  simp only [toCompletedDiagram_diagram, ← FiniteWallDiagram.equivalent_def]
  exact forall_congr' fun k => D.levelEquivalent_iff_toKSComplex E k

/-- Presentation equivalence is reflexive. -/
@[refl]
theorem Equivalent.refl : D.Equivalent D := fun k => LevelEquivalent.refl D k

variable {D E}

/-- Presentation equivalence is symmetric. -/
@[symm]
theorem Equivalent.symm (hDE : D.Equivalent E) : E.Equivalent D := fun k => (hDE k).symm

/-- Presentation equivalence is transitive. -/
@[trans]
theorem Equivalent.trans (hDE : D.Equivalent E) (hEF : E.Equivalent F) : D.Equivalent F :=
  fun k => (hDE k).trans (hEF k)

end Mei.IndexedWallPresentation
