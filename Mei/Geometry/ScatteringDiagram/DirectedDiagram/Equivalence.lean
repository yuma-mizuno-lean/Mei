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

Agreement at one cutoff descends to every lower cutoff. Move lower-order test
paths into general position for both higher active families, compare there,
and project the products using `DirectedDiagram.truncation_levelPathProduct`.
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

/-- Prefixing a stationary segment at the start gives a path with a repeated initial
vertex and the same finite-order product. -/
theorem exists_vertices_eq_cons_levelPathProduct_eq (D : DirectedDiagram (d := d) h H ι) (k : ℕ)
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

/-- A loop can be moved into the complement of any finite family of codimension-one
convex polyhedra, preserving its finite-order product on every admissible path
with the new ambient vertex list. The basepoint moves with both ends of the loop. -/
theorem exists_loop_levelPathProduct_eq_of_vertices_eq
    (D : DirectedDiagram (d := d) h H ι) (k : ℕ)
    {κ : Type*} [Finite κ] (W : κ → Set V)
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    {x : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x x) :
    ∃ z : WallComplement W, ∃ q : AdmissiblePLPath z z,
      ∀ {x' y' : WallComplement (fun j : D.active k => (D.wall j).support)}
        (s : AdmissiblePLPath x' y'),
        s.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
          D.levelPathProduct k s = D.levelPathProduct k p := by
  let := h.finiteDimensional
  -- Stationary padding also covers the loop with no edges.
  obtain ⟨p', hvp, hprod⟩ := D.exists_vertices_eq_cons_levelPathProduct_eq k p
  obtain ⟨ε, hε, hp⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p'
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [x.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  obtain ⟨z, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt hpoly hdim x.val
    (l := x.val :: p.vertices.dropLast.map WallComplement.val) hε
  refine ⟨z, q, fun s hs => ?_⟩
  exact (hp s (by rwa [hv, hs])).trans hprod

variable (D F) in
/-- Two finite-order tests with the same ambient vertices can be realized in any
countable collection of finite polyhedral wall families. Both products are preserved
by every admissible realization of the new vertex list; endpoints may move. -/
theorem exists_common_levelPathProduct_eq (k l : ℕ)
    {J : Type*} {I : J → Type*} [Countable J] [∀ j, Finite (I j)]
    {W : ∀ j, I j → Set V}
    (hpoly : ∀ j a, TauCeti.IsConvexPolyhedron (W j a))
    (hdim : ∀ j a, Module.finrank ℝ (affineSpan ℝ (W j a)).direction + 1 =
      Module.finrank ℝ V)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : F.active l => (F.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    ∃ (a b : CommonWallComplement W) (r : Quiver.Path a b),
      (∀ {u v : WallComplement (fun j : D.active k => (D.wall j).support)}
        (s : AdmissiblePLPath u v),
        s.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val →
          D.levelPathProduct k s = D.levelPathProduct k p) ∧
      (∀ {u v : WallComplement (fun j : F.active l => (F.wall j).support)}
        (s : AdmissiblePLPath u v),
        s.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val →
          F.levelPathProduct l s = F.levelPathProduct l q) := by
  let := h.finiteDimensional
  -- Stationary padding supplies a free interior vertex even for constant paths.
  obtain ⟨p', hvp, hprodP⟩ := D.exists_vertices_eq_cons_levelPathProduct_eq k p
  obtain ⟨q', hvq, hprodQ⟩ := F.exists_vertices_eq_cons_levelPathProduct_eq l q
  have hx : x.val = x'.val := by simpa using congrArg List.head? hpq
  have hvpq : p'.vertices.map WallComplement.val = q'.vertices.map WallComplement.val := by
    rw [hvp, hvq, hx, hpq]
  obtain ⟨ε₁, hε₁, hp⟩ := D.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p'
  obtain ⟨ε₂, hε₂, hq⟩ := F.exists_pos_levelPathProduct_eq_of_forall₂_dist_lt l q'
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [y.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  -- Move all vertices within both stability radii, then recover the test products.
  obtain ⟨a, b, r, hr⟩ := CommonWallComplement.exists_forall₂_dist_lt_free_endpoints
    hpoly hdim x.val y.val (l := x.val :: p.vertices.dropLast.map WallComplement.val)
    (List.cons_ne_nil _ _) (lt_min hε₁ hε₂)
  refine ⟨a, b, r, ?_, ?_⟩
  · intro u v s hs
    apply Eq.trans (hp s ?_) hprodP
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_left ε₁ ε₂)
    rwa [← hv, ← hs] at hnear
  · intro u v s hs
    apply Eq.trans (hq s ?_) hprodQ
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_right ε₁ ε₂)
    rwa [← hv, hvpq, ← hs] at hnear

/-- Finite-order equivalence is transitive, even when the original test path's
endpoints lie on active walls of the intermediate diagram. -/
@[trans]
theorem LevelEquivalent.trans {k : ℕ} (hDE : D.LevelEquivalent E k)
    (hEF : E.LevelEquivalent F k) : D.LevelEquivalent F k := by
  intro x y x' y' p q hpq
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
  obtain ⟨a, b, r, hP, hQ⟩ := D.exists_common_levelPathProduct_eq F k k
    hpoly hdim p q hpq
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
  calc
    D.levelPathProduct k p = D.levelPathProduct k r₁ := (hP r₁ hv₁).symm
    _ = E.levelPathProduct k r₂ := hDE r₁ r₂ (hv₁.trans hv₂.symm)
    _ = F.levelPathProduct k r₃ := hEF r₂ r₃ (hv₂.trans hv₃.symm)
    _ = F.levelPathProduct k q := hQ r₃ hv₃

/-- Agreement at a higher cutoff implies agreement at every lower cutoff.
The lower-order test paths may meet walls that are active only at the higher order. -/
theorem LevelEquivalent.mono {k l : ℕ} (hDE : D.LevelEquivalent E l) (hkl : k ≤ l) :
    D.LevelEquivalent E k := by
  intro x y x' y' p q hpq
  let W : D.active l ⊕ E.active l → Set V :=
    Sum.elim (fun j => (D.wall j).support) (fun j => (E.wall j).support)
  have hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j) := by
    rintro (j | j)
    · exact (D.wall j).isConvexPolyhedron
    · exact (E.wall j).isConvexPolyhedron
  have hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V := by
    rintro (j | j)
    · exact (D.wall j).finrank_direction_add_one
    · exact (E.wall j).finrank_direction_add_one
  obtain ⟨a, b, r, hP, hQ⟩ := D.exists_common_levelPathProduct_eq E k k
    (W := fun _ : Unit => W) (fun _ => hpoly) (fun _ => hdim) p q hpq
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  let rD := (WallComplement.restrictPrefunctor W Sum.inl).mapPath r₀
  let rE := (WallComplement.restrictPrefunctor W Sum.inr).mapPath r₀
  have hvD : rD.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor W Sum.inl r₀).trans
      (CommonWallComplement.vertices_projection () r)
  have hvE : rE.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor W Sum.inr r₀).trans
      (CommonWallComplement.vertices_projection () r)
  let fD := WallComplement.restrictPrefunctor
    (fun j : D.active l => (D.wall j).support) (Set.inclusion (D.active_mono hkl))
  let fE := WallComplement.restrictPrefunctor
    (fun j : E.active l => (E.wall j).support) (Set.inclusion (E.active_mono hkl))
  have hlowD := hP (fD.mapPath rD)
    ((WallComplement.vertices_restrictPrefunctor
      (fun j : D.active l => (D.wall j).support)
      (Set.inclusion (D.active_mono hkl)) rD).trans hvD)
  have hlowE := hQ (fE.mapPath rE)
    ((WallComplement.vertices_restrictPrefunctor
      (fun j : E.active l => (E.wall j).support)
      (Set.inclusion (E.active_mono hkl)) rE).trans hvE)
  calc
    _ = D.levelPathProduct k (fD.mapPath rD) := hlowD.symm
    _ = (d.truncationMap ℒ hkl).bchGroupMap (D.levelPathProduct l rD) :=
      (D.truncation_levelPathProduct hkl rD).symm
    _ = (d.truncationMap ℒ hkl).bchGroupMap (E.levelPathProduct l rE) :=
      congrArg (d.truncationMap ℒ hkl).bchGroupMap (hDE rD rE (hvD.trans hvE.symm))
    _ = E.levelPathProduct k (fE.mapPath rE) := E.truncation_levelPathProduct hkl rE
    _ = _ := hlowE

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
