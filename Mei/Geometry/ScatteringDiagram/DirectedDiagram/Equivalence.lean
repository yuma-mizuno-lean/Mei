/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Completion
public import Mei.Geometry.Convex.Polyhedron.Path.Perturbation

/-!
# Equivalence of directed diagrams

Directed diagrams agree at a cutoff when their products agree on every common
admissible polygonal vertex list. This is an equivalence relation even if the
vertices of a test path lie on walls of an intermediate diagram: move all vertices
into common general position, retaining the products in the two original diagrams.
Coincident indexed walls remain separate factors in each simultaneous crossing.

The proof follows the common-path argument for `FiniteWallDiagram.Equivalent`,
using the signed-event stability of
`Quiver.Path.exists_pos_signedCrossingEvents_eq_of_forall₂_dist_lt` for arbitrary
wall families. Agreement at every cutoff also identifies the completed products.
No local finiteness of the union of the active supports is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe uι uκ uη

variable {Γ Λ R L V : Type*} {ι : Type uι} {κ : Type uκ} {η : Type uη}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι)
  (E : DirectedDiagram (d := d) h H κ)
  (F : DirectedDiagram (d := d) h H η)

/-- Every finite-order directed transport is stable under small movements of all
vertices, including endpoints. -/
theorem exists_pos_levelPathProduct_eq_of_forall₂_dist_lt (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ∃ ε > 0, ∀ {x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
      (q : AdmissiblePLPath x' y'),
      List.Forall₂ (fun a b => dist a b < ε) (p.vertices.map WallComplement.val)
        (q.vertices.map WallComplement.val) → D.levelPathProduct k q = D.levelPathProduct k p := by
  let := h.finiteDimensional
  obtain ⟨ε, hε, hp⟩ := p.exists_pos_wallPathProduct_eq_of_forall₂_dist_lt
    (G := d.truncatedGroup ℒ k)
    (fun j : D.active k => (D.wall j).isConvexPolyhedron.isClosed)
    (fun j => (D.wall j).finrank_direction_add_one)
    (fun j => h.realCharacter (D.wall j).normal)
    (fun j => (D.wall j).direction_support.symm)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.activeLabels_commute k)
  refine ⟨ε, hε, fun q hq => ?_⟩
  rw [D.levelPathProduct_eq_wallPathProduct k q (D.activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact hp q hq

/-- The finite-order product depends only on the ambient vertex list. -/
theorem levelPathProduct_eq_of_vertices_eq (k : ℕ)
    {x y x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    D.levelPathProduct k p = D.levelPathProduct k q := by
  obtain ⟨ε, hε, hp⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p
  apply (hp q _).symm
  rw [hpq]
  exact List.forall₂_same.mpr fun _ _ => by simpa using hε

/-- Agreement of the actual active-wall products on every common admissible vertex
list at order `k`. The two indexed wall families may differ. -/
def LevelEquivalent (k : ℕ) : Prop :=
  ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
    ⦃x' y' : WallComplement (fun j : E.active k => (E.wall j).support)⦄
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
    p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
      D.levelPathProduct k p = E.levelPathProduct k q

/-- The common-path characterization of finite-order equivalence. -/
theorem levelEquivalent_def (k : ℕ) : D.LevelEquivalent E k ↔
    ∀ ⦃x y : WallComplement (fun j : D.active k => (D.wall j).support)⦄
      ⦃x' y' : WallComplement (fun j : E.active k => (E.wall j).support)⦄
      (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
      p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
        D.levelPathProduct k p = E.levelPathProduct k q := Iff.rfl

/-- Every directed diagram agrees with itself at every cutoff. -/
theorem LevelEquivalent.refl (k : ℕ) : D.LevelEquivalent D k := by
  intro x y x' y' p q hpq
  exact D.levelPathProduct_eq_of_vertices_eq k p q hpq

variable {D E F}

/-- Finite-order equivalence is symmetric. -/
@[symm]
theorem LevelEquivalent.symm {k : ℕ} (hDE : D.LevelEquivalent E k) :
    E.LevelEquivalent D k := by
  intro x y x' y' p q hpq
  exact (hDE q p hpq.symm).symm

private theorem exists_padded_path (D : DirectedDiagram (d := d) h H ι) (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ∃ q : AdmissiblePLPath x y,
      q.vertices.map WallComplement.val = x.val :: x.val :: p.vertices.map WallComplement.val ∧
      D.levelPathProduct k q = D.levelPathProduct k p := by
  let e : x ⟶ x := ⟨WallComplement.AdmissibleSegment.refl _ (by
    intro hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion
      (fun j : D.active k => (D.wall j).support)
      (fun j => (D.wall j).isConvexPolyhedron.isClosed) hs)
    exact x.notMem j hj)⟩
  refine ⟨(e.toPath.cons e).comp p, ?_, ?_⟩
  · simp only [Quiver.Path.vertices_comp, Quiver.Path.vertices_cons,
      Quiver.Path.vertices_toPath, List.concat_eq_append, List.cons_append,
      List.nil_append, List.dropLast_cons_cons, List.dropLast_singleton, List.map_cons]
  · have he : D.levelPathProduct k e.toPath = 1 := by
      rw [D.levelPathProduct_eq_wallPathProduct k e.toPath (D.activeLabels_commute k)]
      simp
      -- The concrete BCH identity agrees with the categorical tower identity.
      rfl
    simp [he]

/-- Finite-order equivalence is transitive, even when the original test path's
endpoints lie on active walls of the intermediate diagram. -/
@[trans]
theorem LevelEquivalent.trans {k : ℕ} (hDE : D.LevelEquivalent E k)
    (hEF : E.LevelEquivalent F k) : D.LevelEquivalent F k := by
  intro x y x' y' p q hpq
  let := h.finiteDimensional
  -- Stationary padding gives free interior vertices without changing either product.
  obtain ⟨p', hvp, hprodP⟩ := exists_padded_path D k p
  obtain ⟨q', hvq, hprodQ⟩ := exists_padded_path F k q
  have hx : x.val = x'.val := by
    have he := congrArg List.head? hpq
    simpa using he
  have hvpq : p'.vertices.map WallComplement.val = q'.vertices.map WallComplement.val := by
    rw [hvp, hvq, hx, hpq]
  obtain ⟨ε₁, hε₁, hp⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p'
  obtain ⟨ε₂, hε₂, hq⟩ := F.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k q'
  -- Lift only the finite indices, so the three diagrams may use different universes.
  let I : Option Bool → Type _
    | none => ULift.{max uι uκ uη} (E.active k)
    | some false => ULift.{max uι uκ uη} (D.active k)
    | some true => ULift.{max uι uκ uη} (F.active k)
  let W : ∀ j, I j → Set V
    | none, a => (E.wall a.down).support
    | some false, a => (D.wall a.down).support
    | some true, a => (F.wall a.down).support
  have hpoly : ∀ j a, TauCeti.IsConvexPolyhedron (W j a) := by
    intro j
    cases j with
    | none => exact fun a => (E.wall a.down).isConvexPolyhedron
    | some b => cases b <;>
        [exact fun a => (D.wall a.down).isConvexPolyhedron;
         exact fun a => (F.wall a.down).isConvexPolyhedron]
  have hdim : ∀ j a, Module.finrank ℝ (affineSpan ℝ (W j a)).direction + 1 =
      Module.finrank ℝ V := by
    intro j
    cases j with
    | none => exact fun a => (E.wall a.down).finrank_direction_add_one
    | some b => cases b <;>
        [exact fun a => (D.wall a.down).finrank_direction_add_one;
         exact fun a => (F.wall a.down).finrank_direction_add_one]
  have : ∀ j, Finite (I j) := by
    intro j
    cases j with
    | none => dsimp [I]; infer_instance
    | some b => cases b <;> dsimp [I] <;> infer_instance
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [y.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  -- Move endpoints as well as interior vertices, within both product-stability radii.
  obtain ⟨a, b, r, hr⟩ := CommonWallComplement.exists_forall₂_dist_lt_free_endpoints
    hpoly hdim x.val y.val
    (l := x.val :: p.vertices.dropLast.map WallComplement.val)
    (List.cons_ne_nil _ _) (lt_min hε₁ hε₂)
  -- Project the new path to all three families and recover the two test products.
  let r₁ := (WallComplement.restrictPrefunctor (W (some false)) ULift.up).mapPath
    ((CommonWallComplement.projectionPrefunctor (some false)).mapPath r)
  let r₂ := (WallComplement.restrictPrefunctor (W none) ULift.up).mapPath
    ((CommonWallComplement.projectionPrefunctor none).mapPath r)
  let r₃ := (WallComplement.restrictPrefunctor (W (some true)) ULift.up).mapPath
    ((CommonWallComplement.projectionPrefunctor (some true)).mapPath r)
  have hv₁ : r₁.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection (some false) r)
  have hv₂ : r₂.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection none r)
  have hv₃ : r₃.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection (some true) r)
  have hP : D.levelPathProduct k r₁ = D.levelPathProduct k p' := by
    apply hp
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_left _ _)
    rw [← hv] at hnear
    exact hv₁.symm ▸ hnear
  have hQ : F.levelPathProduct k r₃ = F.levelPathProduct k q' := by
    apply hq
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_right _ _)
    rw [← hv, hvpq] at hnear
    exact hv₃.symm ▸ hnear
  calc
    D.levelPathProduct k p = D.levelPathProduct k r₁ := hprodP.symm.trans hP.symm
    _ = E.levelPathProduct k r₂ := hDE r₁ r₂ (hv₁.trans hv₂.symm)
    _ = F.levelPathProduct k r₃ := hEF r₂ r₃ (hv₂.trans hv₃.symm)
    _ = F.levelPathProduct k q := hQ.trans hprodQ

variable (D E)

/-- Directed diagrams are equivalent when they agree on common paths at every cutoff. -/
def Equivalent : Prop := ∀ k, D.LevelEquivalent E k

/-- Equivalence is exactly finite-order equivalence at every order. -/
theorem equivalent_iff : D.Equivalent E ↔ ∀ k, D.LevelEquivalent E k := Iff.rfl

/-- Every directed diagram is equivalent to itself. -/
@[refl]
theorem Equivalent.refl : D.Equivalent D := fun k => LevelEquivalent.refl D k

variable {D E}

/-- Directed equivalence is symmetric. -/
@[symm]
theorem Equivalent.symm (hDE : D.Equivalent E) : E.Equivalent D := fun k => (hDE k).symm

/-- Directed equivalence is transitive. -/
@[trans]
theorem Equivalent.trans (hDE : D.Equivalent E) (hEF : E.Equivalent F) :
    D.Equivalent F := fun k => (hDE k).trans (hEF k)

/-- Equivalent directed diagrams have equal completed products on common all-order paths. -/
theorem Equivalent.pathProduct_eq (hDE : D.Equivalent E)
    {x y : D.Point} {x' y' : E.Point} (p : Quiver.Path x y) (q : Quiver.Path x' y')
    (hpq : p.vertices.map CommonWallComplement.val =
      q.vertices.map CommonWallComplement.val) : D.pathProduct p = E.pathProduct q := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_pathProduct]
  apply hDE k
  exact (CommonWallComplement.vertices_projection k p).trans
    (hpq.trans (CommonWallComplement.vertices_projection k q).symm)

end Mei.DirectedDiagram
