/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency

/-!
# Consistency and transport under directed equivalence

Equivalent directed diagrams have the same consistency behavior at every cutoff.
Their finite and completed endpoint transports agree whenever both endpoint
presentations denote the same ambient points. In particular, consistency and
transport survive changes of wall presentation by refinement.

The loop argument follows `FiniteWallDiagram.Equivalent.consistent`, using
`AdmissiblePLPath.exists_loop_forall₂_dist_lt` to keep perturbed paths closed.
Product stability here uses simultaneous signed crossing events, so repeated and
overlapping coplanar walls are retained. Common paths compare endpoint transport;
no stabilization or local finiteness of the union of active walls is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H κ}

/-- Finite-order equivalence preserves consistency, even when the basepoint of
a test loop lies on active walls of the other diagram. -/
theorem LevelEquivalent.consistent {k : ℕ} (hDE : D.LevelEquivalent E k)
    (hD : D.LevelConsistent k) : E.LevelConsistent k := by
  apply (E.levelConsistent_iff_loops k).mpr
  intro x p
  let W : E.active k ⊕ D.active k → Set V :=
    Sum.elim (fun j => (E.wall j).support) (fun j => (D.wall j).support)
  have hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j) := by
    rintro (j | j)
    · exact (E.wall j).isConvexPolyhedron
    · exact (D.wall j).isConvexPolyhedron
  have hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V := by
    rintro (j | j)
    · exact (E.wall j).finrank_direction_add_one
    · exact (D.wall j).finrank_direction_add_one
  obtain ⟨a, q, hq⟩ := E.exists_loop_levelPathProduct_eq_of_vertices_eq k W hpoly hdim p
  let qE : AdmissiblePLPath
      (⟨a.val, fun j => a.notMem (.inl j)⟩ :
        WallComplement (fun j : E.active k => (E.wall j).support))
      ⟨a.val, fun j => a.notMem (.inl j)⟩ :=
    (WallComplement.restrictPrefunctor W Sum.inl).mapPath q
  let qD : AdmissiblePLPath
      (⟨a.val, fun j => a.notMem (.inr j)⟩ :
        WallComplement (fun j : D.active k => (D.wall j).support))
      ⟨a.val, fun j => a.notMem (.inr j)⟩ :=
    (WallComplement.restrictPrefunctor W Sum.inr).mapPath q
  have hvE : qE.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor W Sum.inl q
  have hvD : qD.vertices.map WallComplement.val = q.vertices.map WallComplement.val :=
    WallComplement.vertices_restrictPrefunctor W Sum.inr q
  calc
    E.levelPathProduct k p = E.levelPathProduct k qE := (hq qE hvE).symm
    _ = D.levelPathProduct k qD :=
      ((levelEquivalent_def D E k).mp hDE qD qE (hvD.trans hvE.symm)).symm
    _ = 1 := (D.levelConsistent_iff_loops k).mp hD _ qD

/-- Equivalent directed presentations have the same consistency at a fixed order. -/
theorem LevelEquivalent.consistent_iff {k : ℕ} (hDE : D.LevelEquivalent E k) :
    D.LevelConsistent k ↔ E.LevelConsistent k :=
  ⟨hDE.consistent, hDE.symm.consistent⟩

/-- Equivalence preserves consistency at every cutoff. -/
theorem Equivalent.consistent (hDE : D.Equivalent E) (hD : D.Consistent) : E.Consistent :=
  (E.consistent_iff).mpr fun k =>
    ((equivalent_iff D E).mp hDE k).consistent ((D.consistent_iff).mp hD k)

/-- Consistency depends only on the equivalence class of a directed diagram. -/
theorem Equivalent.consistent_iff (hDE : D.Equivalent E) : D.Consistent ↔ E.Consistent :=
  ⟨hDE.consistent, hDE.symm.consistent⟩

/-- Finite endpoint transport in equivalent consistent diagrams agrees at common
ambient endpoints, independently of the chosen endpoint presentations. -/
theorem LevelEquivalent.levelTransport_eq {k : ℕ} (hDE : D.LevelEquivalent E k)
    (hD : D.LevelConsistent k) (hE : E.LevelConsistent k)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    {x' y' : WallComplement (fun j : E.active k => (E.wall j).support)}
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    D.levelTransport k hD x y = E.levelTransport k hE x' y' := by
  let := h.finiteDimensional
  let W : D.active k ⊕ E.active k → Set V :=
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
  let a : WallComplement W := ⟨x.val, by
    rintro (j | j)
    · exact x.notMem j
    · simpa only [W, Sum.elim_inr, hx] using x'.notMem j⟩
  let b : WallComplement W := ⟨y.val, by
    rintro (j | j)
    · exact y.notMem j
    · simpa only [W, Sum.elim_inr, hy] using y'.notMem j⟩
  obtain ⟨p, _⟩ := AdmissiblePLPath.exists_length_eq_two hpoly hdim a b
  let pD : AdmissiblePLPath
      (⟨a.val, fun j => a.notMem (.inl j)⟩ :
        WallComplement (fun j : D.active k => (D.wall j).support))
      ⟨b.val, fun j => b.notMem (.inl j)⟩ :=
    (WallComplement.restrictPrefunctor W Sum.inl).mapPath p
  let pE : AdmissiblePLPath
      (⟨a.val, fun j => a.notMem (.inr j)⟩ :
        WallComplement (fun j : E.active k => (E.wall j).support))
      ⟨b.val, fun j => b.notMem (.inr j)⟩ :=
    (WallComplement.restrictPrefunctor W Sum.inr).mapPath p
  have he := (levelEquivalent_def D E k).mp hDE pD pE
    ((WallComplement.vertices_restrictPrefunctor W Sum.inl p).trans
      (WallComplement.vertices_restrictPrefunctor W Sum.inr p).symm)
  rw [← D.levelTransport_eq_levelPathProduct hD pD,
    ← E.levelTransport_eq_levelPathProduct hE pE] at he
  have haD : (⟨a.val, fun j => a.notMem (.inl j)⟩ :
      WallComplement (fun j : D.active k => (D.wall j).support)) = x :=
    WallComplement.ext rfl
  have hbD : (⟨b.val, fun j => b.notMem (.inl j)⟩ :
      WallComplement (fun j : D.active k => (D.wall j).support)) = y :=
    WallComplement.ext rfl
  have haE : (⟨a.val, fun j => a.notMem (.inr j)⟩ :
      WallComplement (fun j : E.active k => (E.wall j).support)) = x' :=
    WallComplement.ext hx
  have hbE : (⟨b.val, fun j => b.notMem (.inr j)⟩ :
      WallComplement (fun j : E.active k => (E.wall j).support)) = y' :=
    WallComplement.ext hy
  simpa only [haD, hbD, haE, hbE] using he

/-- Equivalent consistent directed diagrams have equal completed transport at
common all-order endpoints. No common choice of all-order path is required. -/
theorem Equivalent.transport_eq (hDE : D.Equivalent E) (hD : D.Consistent)
    (hE : E.Consistent) {x y : D.Point} {x' y' : E.Point}
    (hx : x.val = x'.val) (hy : y.val = y'.val) :
    D.transport hD x y = E.transport hE x' y' := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_transport_eq_levelTransport]
  exact ((equivalent_iff D E).mp hDE k).levelTransport_eq
    ((D.consistent_iff).mp hD k) ((E.consistent_iff).mp hE k) hx hy

end Mei.DirectedDiagram
