/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Recession
public import Mathlib.Topology.Order.Compact

/-!
# Uniform escape from a polyhedron

A direction outside a polyhedron's recession cone has strictly positive value
under a continuous linear functional bounded above on the polyhedron. Hence
translating any compact set sufficiently far in that direction misses the entire
polyhedron, with a single bound for every point of the compact set.

This uses the affine inequalities in `TauCeti.isConvexPolyhedron_iff` and their
homogeneous recession inequalities in `Set.mem_recessionCone_setOf_forall_iff`.
Uniformity follows from Mathlib's `IsCompact.bddBelow_image`. Neither finite
dimensionality nor boundedness of the polyhedron is required.
-/

public section

open Set Filter

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {v : V}

/-- A direction outside a polyhedron's recession cone is strictly positive for
a continuous linear functional bounded above on that polyhedron. -/
theorem exists_pos_bound_of_notMem_recessionCone (hP : TauCeti.IsConvexPolyhedron P)
    (hv : v ∉ recessionCone P) :
    ∃ (f : V →L[ℝ] ℝ) (c : ℝ), 0 < f v ∧ ∀ x ∈ P, f x ≤ c := by
  have hne : P.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, recessionCone_empty] at hv
    exact hv (by trivial)
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  have hn : ¬∀ j, (g j).toAffineMap.linear v ≤ 0 :=
    fun hj => hv ((mem_recessionCone_setOf_forall_iff hne).mpr hj)
  push Not at hn
  obtain ⟨j, hj⟩ := hn
  refine ⟨(g j).contLinear, -g j 0, hj, fun x hx => ?_⟩
  have he : g j x = (g j).contLinear x + g j 0 := by
    exact congrFun (g j).decomp x
  linarith [hx j]

/-- Compact sets translated far enough in a nonrecession direction uniformly
miss the polyhedron. The initial compact set may meet the polyhedron. -/
theorem eventually_forall_notMem_of_notMem_recessionCone
    (hP : TauCeti.IsConvexPolyhedron P) (hv : v ∉ recessionCone P)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • v ∉ P := by
  obtain ⟨f, c, hfv, hfP⟩ := exists_pos_bound_of_notMem_recessionCone hP hv
  obtain ⟨b, hb⟩ := hK.bddBelow_image f.continuous.continuousOn
  filter_upwards [eventually_gt_atTop ((c - b) / f v)] with t ht x hx hmem
  have htf : c - b < t * f v := (div_lt_iff₀ hfv).mp ht
  have hbx : b ≤ f x := hb (mem_image_of_mem f hx)
  have hup := hfP (x + t • v) hmem
  simp only [map_add, map_smul, smul_eq_mul] at hup
  linarith

/-- For a nonempty polyhedron, uniform escape of every compact set characterizes
directions outside the recession cone. -/
theorem notMem_recessionCone_iff_eventually_forall_notMem
    (hP : TauCeti.IsConvexPolyhedron P) (hne : P.Nonempty) :
    v ∉ recessionCone P ↔
      ∀ K : Set V, IsCompact K → ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, x + t • v ∉ P := by
  constructor
  · exact fun hv _ hK => eventually_forall_notMem_of_notMem_recessionCone hP hv hK
  · intro he hv
    obtain ⟨x, hx⟩ := hne
    obtain ⟨t, ht, hpos⟩ := ((he {x} isCompact_singleton).and (eventually_ge_atTop 0)).exists
    exact ht x (mem_singleton x) ((mem_recessionCone.mp hv) x hx t hpos)

end Mei.Convex
