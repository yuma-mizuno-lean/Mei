/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.Convex.Polyhedron.Escape
public import Mei.Geometry.Convex.Polyhedron.Path.Escape

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

Consequently, consider additive coefficients on finitely many directed walls, nonzero
only on outgoing walls whose rays carry a common degree `n`. If their signed crossing
sum vanishes around every admissible loop at a point, it vanishes along every
admissible path from that point.
This is `Quiver.Path.wallCrossingSum_eq_zero_of_notMem_recessionCone` for the geometric
direction of `n`: it vanishes on the normals of those walls and is not a recession
direction of their supports. Walls with zero coefficient are unrestricted.
-/

public section

open Set Filter Mei.Convex WallComplement

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

/-- No actual degree on an outgoing wall's ray is a recession direction of its support. -/
theorem Outgoing.notMem_recessionCone_of_mem_rayDegrees (hW : W.Outgoing)
    {n : Γ} (hn : n ∈ W.ray.rayDegrees) : i (ρ n) ∉ recessionCone W.support := by
  intro hv
  have hinc := (W.incoming_iff_of_mem_rayDegrees hn).mpr hv
  exact (W.outgoing_iff.mp hW) (mem_recessionCone.mpr (W.incoming_iff.mp hinc))

/-- Any actual nonzero degree on an outgoing wall's ray gives the same uniform
escape, even when the primitive generator is not itself allowed. -/
theorem Outgoing.eventually_forall_notMem_support_of_mem_rayDegrees (hW : W.Outgoing)
    {n : Γ} (hn : n ∈ W.ray.rayDegrees) {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • i (ρ n) ∉ W.support :=
  eventually_forall_notMem_of_notMem_recessionCone W.isConvexPolyhedron
    (hW.notMem_recessionCone_of_mem_rayDegrees hn) hK

/-- A crossing sum vanishing around all admissible loops at `x` vanishes along all
admissible paths from `x`, if each wall with nonzero coefficient is outgoing with `n`
on its ray. -/
theorem wallCrossingSum_eq_zero_of_outgoing {ι E : Type*} [Finite ι] [AddCommGroup E]
    (W : ι → DirectedWall (d := d) h H) (c : ι → E) {n : Γ}
    (hout : ∀ j, c j ≠ 0 → (W j).Outgoing ∧ n ∈ (W j).ray.rayDegrees)
    {x y : WallComplement fun j => (W j).support}
    (hloop : ∀ q : AdmissiblePLPath x x,
      q.wallCrossingSum (fun j => h.realCharacter (W j).normal) c = 0)
    (p : AdmissiblePLPath x y) :
    p.wallCrossingSum (fun j => h.realCharacter (W j).normal) c = 0 := by
  let := h.finiteDimensional
  refine p.wallCrossingSum_eq_zero_of_notMem_recessionCone (fun j => (W j).isConvexPolyhedron)
    (fun j => (W j).finrank_direction_add_one) _ (fun j => (W j).direction_support.symm) c
    (v := i (ρ n)) (fun j hj => ?_) (fun j hj => ?_) hloop
  · obtain ⟨-, a, -, rfl⟩ := SupportedRay.mem_rayDegrees.mp (hout j hj).2
    simp [h.realCharacter_apply, (W j).normal_direction]
  · exact (hout j hj).1.notMem_recessionCone_of_mem_rayDegrees (hout j hj).2

end Mei.DirectedWall
