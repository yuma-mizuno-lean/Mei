/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.Convex.PolyhedralComplex.CommonPerturbation

/-!
# Detecting completed diagram equivalence by complete products

Two completed KS diagrams are equivalent when their finite products agree on
common admissible vertex lists at every order. Equivalently, their completed
products agree on every common all-order path. The converse includes finite tests
whose endpoints lie on walls at other orders: move all vertices into simultaneous
general position, preserving the two prescribed finite crossing words, then project
the resulting complete-product equality.
`CompletedDiagram.exists_common_pathProduct_eq` exposes these all-order paths, whose
projected products are the two prescribed finite products.

No relation between the two sequences of complexes is required. In particular,
the complexes need not stabilize or refine one another, and neither diagram needs
to be consistent. The geometric input is
`CommonWallComplement.exists_free_endpoints_crossingWord_eq_of_vertices_eq`,
combining the existing crossing-word stability theorem with countable Baire
perturbation. The equivalence is the compatible finite-diagram equivalence in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), Definition 2.3.
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

/-- Completed diagrams are equivalent if their actual geometric products agree
at each order on every vertex list admissible for both finite diagrams. -/
def Equivalent : Prop :=
  ∀ k {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
    {x' y' : WallComplement (fun P : (E k).walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
    p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
      (D.diagram k).toFiniteWallDiagram.pathProduct p =
        (F.diagram k).toFiniteWallDiagram.pathProduct q

/-- The finite-order common-path characterization of completed equivalence. -/
theorem equivalent_iff : D.Equivalent F ↔
    ∀ k {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
      {x' y' : WallComplement (fun P : (E k).walls => (P : Set V))}
      (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
      p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
        (D.diagram k).toFiniteWallDiagram.pathProduct p =
          (F.diagram k).toFiniteWallDiagram.pathProduct q := Iff.rfl

variable {D F}

/-- Equivalent completed diagrams have equal products on common all-order paths. -/
theorem Equivalent.pathProduct_eq (hDF : D.Equivalent F)
    {x y : Point C} {x' y' : Point E} (p : Quiver.Path x y) (q : Quiver.Path x' y')
    (hpq : p.vertices.map CommonWallComplement.val =
      q.vertices.map CommonWallComplement.val) : D.pathProduct p = F.pathProduct q := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_pathProduct]
  apply (equivalent_iff D F).mp hDF k
  exact (CommonWallComplement.vertices_projection k p).trans
    (hpq.trans (CommonWallComplement.vertices_projection k q).symm)

variable (D F)

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

/-- Equality on all common all-order paths detects every finite test product,
even when the original finite test has endpoints on walls at other cutoffs. -/
theorem equivalent_of_pathProduct_eq
    (hDF : ∀ {x y : Point C} {x' y' : Point E}
      (p : Quiver.Path x y) (q : Quiver.Path x' y'),
      p.vertices.map CommonWallComplement.val = q.vertices.map CommonWallComplement.val →
        D.pathProduct p = F.pathProduct q) : D.Equivalent F := by
  rw [equivalent_iff]
  intro k x y x' y' p q hpq
  -- Realize both tests by common all-order paths, then project the complete equality.
  obtain ⟨_, _, _, _, p', q', hv, hp, hq⟩ := D.exists_common_pathProduct_eq F k p q hpq
  exact hp.symm.trans ((congrArg (CompletedGroup.projection k) (hDF p' q' hv)).trans hq)

/-- Complete geometric products detect precisely orderwise equivalence.
Both directions compare the same ambient vertex lists, with separate admissibility
for each diagram. -/
theorem equivalent_iff_pathProduct_eq : D.Equivalent F ↔
    ∀ {x y : Point C} {x' y' : Point E} (p : Quiver.Path x y) (q : Quiver.Path x' y'),
      p.vertices.map CommonWallComplement.val = q.vertices.map CommonWallComplement.val →
        D.pathProduct p = F.pathProduct q := by
  constructor
  · intro hDF x y x' y' p q hpq
    exact hDF.pathProduct_eq p q hpq
  · exact D.equivalent_of_pathProduct_eq F

end Mei.CompletedDiagram
