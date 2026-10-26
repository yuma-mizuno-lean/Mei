/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.Polyhedron.Escape

/-!
# Far translates miss outgoing walls

An outgoing wall lies in a linear half-space whose defining functional is
strictly positive in its positive geometric degree direction. Every compact
set, including a transverse path or the boundary of a rectangle, eventually
misses the wall under translation in that direction. The conclusion is uniform
over the compact set and holds for every actual degree on its supported ray.

This is the geometric escape step in the uniqueness argument of
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Theorem 2.6, [arXiv:1503.06183](https://arxiv.org/abs/1503.06183).
It uses `Mei.Convex.exists_pos_bound_of_notMem_recessionCone` and the uniform
compact-escape theorem on the existing `DirectedWall.support` carrier.
-/

public section

open Set Filter Mei.Convex

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  {W : DirectedWall (d := d) h H}

/-- An outgoing support admits a global linear bound positive on its geometric
degree direction. -/
theorem Outgoing.exists_pos_bound (hW : W.Outgoing) :
    ∃ (f : V →L[ℝ] ℝ) (c : ℝ),
      0 < f (i (ρ W.ray.generator)) ∧ ∀ x ∈ W.support, f x ≤ c :=
  exists_pos_bound_of_notMem_recessionCone W.isConvexPolyhedron (W.outgoing_iff.mp hW)

/-- Far positive-degree translates of a compact set uniformly miss an outgoing wall. -/
theorem Outgoing.eventually_forall_notMem_support (hW : W.Outgoing)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • i (ρ W.ray.generator) ∉ W.support :=
  eventually_forall_notMem_of_notMem_recessionCone W.isConvexPolyhedron (W.outgoing_iff.mp hW) hK

/-- Uniform compact escape characterizes outgoingness, including zero spatial directions. -/
theorem outgoing_iff_eventually_forall_notMem_support : W.Outgoing ↔
    ∀ K : Set V, IsCompact K →
      ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • i (ρ W.ray.generator) ∉ W.support :=
  W.outgoing_iff.trans
    (notMem_recessionCone_iff_eventually_forall_notMem W.isConvexPolyhedron W.support_nonempty)

/-- Any actual nonzero degree on an outgoing wall's ray gives the same uniform
escape, even when the primitive generator is not itself allowed. -/
theorem Outgoing.eventually_forall_notMem_support_of_mem_rayDegrees (hW : W.Outgoing)
    {n : Γ} (hn : n ∈ W.ray.rayDegrees) {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • i (ρ n) ∉ W.support := by
  apply eventually_forall_notMem_of_notMem_recessionCone W.isConvexPolyhedron _ hK
  intro hv
  have hinc := (W.incoming_iff_of_mem_rayDegrees hn).mpr hv
  exact (W.outgoing_iff.mp hW) (mem_recessionCone.mpr (W.incoming_iff.mp hinc))

end Mei.DirectedWall
