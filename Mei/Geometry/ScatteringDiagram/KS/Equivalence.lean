/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.ScatteringDiagram.Equivalence

/-!
# Detecting completed diagram equivalence by complete products

Two completed KS diagrams are equivalent when their finite products agree on
common admissible vertex lists at every order. Equivalently, their completed
products agree on every common all-order path. The converse includes finite tests
whose endpoints lie on walls at other orders: move all vertices into simultaneous
general position, preserving the two prescribed finite crossing words, then project
the resulting complete-product equality.

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

/-- Completed diagrams are equivalent if their finite diagrams are equivalent
at each order: their actual geometric products agree on every vertex list
admissible for both finite diagrams. -/
def Equivalent : Prop :=
  ∀ k, (D.diagram k).toFiniteWallDiagram.Equivalent (F.diagram k).toFiniteWallDiagram

/-- The finite-order common-path characterization of completed equivalence. -/
theorem equivalent_iff : D.Equivalent F ↔
    ∀ k {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
      {x' y' : WallComplement (fun P : (E k).walls => (P : Set V))}
      (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
      p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
        (D.diagram k).toFiniteWallDiagram.pathProduct p =
          (F.diagram k).toFiniteWallDiagram.pathProduct q :=
  forall_congr' fun _ => FiniteWallDiagram.equivalent_def _ _

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

/-- Equality on all common all-order paths detects every finite test product,
even when the original finite test has endpoints on walls at other cutoffs. -/
theorem equivalent_of_pathProduct_eq
    (hDF : ∀ {x y : Point C} {x' y' : Point E}
      (p : Quiver.Path x y) (q : Quiver.Path x' y'),
      p.vertices.map CommonWallComplement.val = q.vertices.map CommonWallComplement.val →
        D.pathProduct p = F.pathProduct q) : D.Equivalent F := by
  rw [equivalent_iff]
  intro k x y x' y' p q hpq
  -- Place both towers in one countable family and preserve the two order-k tests.
  let A : ℕ ⊕ ℕ → FinitePolyhedralComplex h := Sum.elim C E
  let a : Bool → ℕ ⊕ ℕ := fun b => if b then .inr k else .inl k
  let ν : (b : Bool) → (A (a b)).walls → V →ₗ[ℝ] ℝ := fun b => by
    cases b
    · exact (D.diagram k).toFiniteWallDiagram.normal
    · exact (F.diagram k).toFiniteWallDiagram.normal
  have hν : ∀ b P, LinearMap.ker (ν b P) = (affineSpan ℝ (P : Set V)).direction := by
    intro b
    cases b
    · exact (D.diagram k).toFiniteWallDiagram.ker_normal
    · exact (F.diagram k).toFiniteWallDiagram.ker_normal
  let X : (b : Bool) → WallComplement (fun P : (A (a b)).walls => (P : Set V)) := fun b => by
    cases b
    · exact x
    · exact x'
  let Y : (b : Bool) → WallComplement (fun P : (A (a b)).walls => (P : Set V)) := fun b => by
    cases b
    · exact y
    · exact y'
  let tests : ∀ b, AdmissiblePLPath (X b) (Y b) := fun b => by
    cases b
    · exact p
    · exact q
  have htests : ∀ b, (tests b).vertices.map WallComplement.val =
      (tests false).vertices.map WallComplement.val := by
    intro b
    cases b
    · rfl
    · exact hpq.symm
  obtain ⟨u, v, r, hr⟩ :=
    CommonWallComplement.exists_free_endpoints_crossingWord_eq_of_vertices_eq
      A a ν hν tests false htests
  let p' := (CommonWallComplement.reindexPrefunctor (W := fun j =>
    fun P : (A j).walls => (P : Set V)) Sum.inl).mapPath r
  let q' := (CommonWallComplement.reindexPrefunctor (W := fun j =>
    fun P : (A j).walls => (P : Set V)) Sum.inr).mapPath r
  have hv : p'.vertices.map CommonWallComplement.val =
      q'.vertices.map CommonWallComplement.val := by
    exact (CommonWallComplement.vertices_reindex Sum.inl r).trans
      (CommonWallComplement.vertices_reindex Sum.inr r).symm
  -- Apply the assumed complete equality, then project back to the selected order.
  have he := congrArg (CompletedGroup.projection k) (hDF p' q' hv)
  rw [D.projection_pathProduct k p', F.projection_pathProduct k q'] at he
  simp only [p', q'] at he
  have hprojLeft := CommonWallComplement.projection_reindex_mapPath
    (W := fun j => fun P : (A j).walls => (P : Set V)) Sum.inl k r
  have hprojRight := CommonWallComplement.projection_reindex_mapPath
    (W := fun j => fun P : (A j).walls => (P : Set V)) Sum.inr k r
  have he' := (congrArg (D.diagram k).toFiniteWallDiagram.pathProduct hprojLeft).symm.trans
    (he.trans (congrArg (F.diagram k).toFiniteWallDiagram.pathProduct hprojRight))
  have hleft := hr false
  have hright := hr true
  -- The sum indices and Boolean cases compute to the two concrete complexes.
  dsimp only [a, Bool.false_eq_true, ↓reduceIte, A, Sum.elim_inl, Sum.elim_inr,
    ν, tests] at hleft hright
  have hleftProd := ((D.diagram k).toFiniteWallDiagram.pathProduct_def
    ((CommonWallComplement.projectionPrefunctor (.inl k)).mapPath r)).trans
    ((congrArg (FreeGroup.lift (D.diagram k).toFiniteWallDiagram.label) hleft).trans
      ((D.diagram k).toFiniteWallDiagram.pathProduct_def p).symm)
  have hrightProd := ((F.diagram k).toFiniteWallDiagram.pathProduct_def
    ((CommonWallComplement.projectionPrefunctor (.inr k)).mapPath r)).trans
    ((congrArg (FreeGroup.lift (F.diagram k).toFiniteWallDiagram.label) hright).trans
      ((F.diagram k).toFiniteWallDiagram.pathProduct_def q).symm)
  exact hleftProd.symm.trans (he'.trans hrightProd)

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
