/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Equivalence
public import Mei.Geometry.Convex.PolyhedralComplex.CommonPerturbation

/-!
# Detecting finite KS products by all-order paths

Every common finite-order test of two completed diagrams is realized by a common
all-order path with the same two projected products. Its endpoints may move: an
endpoint allowed at one cutoff can lie on walls at higher cutoffs. Countable
perturbation preserves the two prescribed crossing words and hence the finite
products. The sequences of complexes need not stabilize or refine one another.

The equivalence criterion is `CompletedDiagram.equivalent_iff_pathProduct_eq`.
Here `CompletedDiagram.exists_common_pathProduct_eq` additionally exposes the
all-order paths realizing any prescribed pair of finite tests, without a consistency
hypothesis or a faithful coefficient action.

This uses `CommonWallComplement.exists_free_endpoints_crossingWord_eq_of_vertices_eq`
and `CompletedDiagram.projection_pathProduct`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.CompletedDiagram

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C E : ℕ → FinitePolyhedralComplex h}
  (D : CompletedDiagram s d ℒ C) (F : CompletedDiagram s d ℒ E)

/-- Two common tests at a finite cutoff can be realized by common all-order paths,
with exactly the original projected products. Endpoints may move to avoid the walls
at every cutoff. No consistency assumption is needed. -/
theorem exists_common_pathProduct_eq (k : ℕ)
    {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
    {x' y' : WallComplement (fun P : (E k).walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    ∃ (u v : Point C) (u' v' : Point E) (p' : Quiver.Path u v) (q' : Quiver.Path u' v'),
      p'.vertices.map CommonWallComplement.val = q'.vertices.map CommonWallComplement.val ∧
      CompletedGroup.projection k (D.pathProduct p') =
        (D.diagram k).toFiniteWallDiagram.pathProduct p ∧
      CompletedGroup.projection k (F.pathProduct q') =
        (F.diagram k).toFiniteWallDiagram.pathProduct q := by
  -- One countable family records both sequences; the two selected tests retain their own normals.
  let a : Bool → ℕ ⊕ ℕ := fun b => if b then Sum.inr k else Sum.inl k
  let diagrams : ∀ b, KSComplex s d ℒ (Sum.elim C E (a b)) k := fun b => by
    cases b
    · exact D.diagram k
    · exact F.diagram k
  let starts : ∀ b : Bool, WallComplement (fun P : (Sum.elim C E (a b)).walls => (P : Set V)) :=
    fun b => by
      cases b
      · exact x
      · exact x'
  let ends : ∀ b : Bool, WallComplement (fun P : (Sum.elim C E (a b)).walls => (P : Set V)) :=
    fun b => by
      cases b
      · exact y
      · exact y'
  let tests : ∀ b : Bool, AdmissiblePLPath (starts b) (ends b) :=
    fun b => by
      cases b
      · exact p
      · exact q
  have htests (b : Bool) : (tests b).vertices.map WallComplement.val =
      (tests false).vertices.map WallComplement.val := by
    cases b
    · rfl
    · exact hpq.symm
  obtain ⟨u, v, r, hr⟩ := CommonWallComplement.exists_free_endpoints_crossingWord_eq_of_vertices_eq
    (Sum.elim C E) a (fun b => (diagrams b).toFiniteWallDiagram.normal)
    (fun b => (diagrams b).toFiniteWallDiagram.ker_normal) tests false htests
  -- Fix the endpoint types before elaborating products, so unification never unfolds
  -- the hidden finite wall inventories of the two selected subfamilies.
  let uC : Point C := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inl).obj u
  let vC : Point C := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inl).obj v
  let uE : Point E := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inr).obj u
  let vE : Point E := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inr).obj v
  let p' : Quiver.Path uC vC := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inl).mapPath r
  let q' : Quiver.Path uE vE := (CommonWallComplement.reindexPrefunctor
    (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inr).mapPath r
  refine ⟨_, _, _, _, p', q', ?_, ?_, ?_⟩
  · exact (CommonWallComplement.vertices_reindex Sum.inl r).trans
      (CommonWallComplement.vertices_reindex Sum.inr r).symm
  · rw [D.projection_pathProduct k p', FiniteWallDiagram.pathProduct_def,
      FiniteWallDiagram.pathProduct_def]
    apply congrArg (FreeGroup.lift (D.diagram k).toFiniteWallDiagram.label)
    have hpr := CommonWallComplement.projection_reindex_mapPath
      (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inl k r
    exact (congrArg (fun t => t.crossingWord (D.diagram k).toFiniteWallDiagram.normal)
      hpr).trans (hr false)
  · rw [F.projection_pathProduct k q', FiniteWallDiagram.pathProduct_def,
      FiniteWallDiagram.pathProduct_def]
    apply congrArg (FreeGroup.lift (F.diagram k).toFiniteWallDiagram.label)
    have hpr := CommonWallComplement.projection_reindex_mapPath
      (W := fun j => fun P : (Sum.elim C E j).walls => (P : Set V)) Sum.inr k r
    exact (congrArg (fun t => t.crossingWord (F.diagram k).toFiniteWallDiagram.normal)
      hpr).trans (hr true)

end Mei.CompletedDiagram
