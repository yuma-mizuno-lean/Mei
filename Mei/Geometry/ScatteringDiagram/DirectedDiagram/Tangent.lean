/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Tangent

/-!
# The tangent diagram at a point

The tangent diagram of a directed diagram at a point `x` retains the walls whose support
contains `x`, each replaced by its tangent wall. Its supports are cones with apex `0`, and
need not be full hyperplanes. For each fixed cutoff `k`, closedness and finiteness of the
active walls give a neighbourhood of `x` on which active walls missing `x` contribute nothing.
This neighbourhood may depend on `k`.

A wall through `x` is active at a cutoff in the tangent diagram exactly when it is active in the
diagram. For each fixed cutoff `k`, on a neighbourhood of `x` depending on `k`, the active
supports are the translates of the tangent supports. At a point in this neighbourhood that is
regular for both diagrams, the combined labels at cutoff `k` agree in each crossing direction
after translating by `x`.
These local identifications compare the crossings of a diagram near a joint with those of its
tangent diagram. Consistency of the tangent diagram is not asserted here.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι) (x : V)

/-- The walls through `x`, each replaced by its tangent wall at `x`. -/
def tangentAt : DirectedDiagram (d := d) h H {j | x ∈ (D.wall j).support} where
  wall j := (D.wall j.1).tangentAt x j.2
  finite_active := by
    simpa only [restrict_wall, DirectedWall.tangentAt_label] using
      (D.restrict {j | x ∈ (D.wall j).support}).finite_active

@[simp]
theorem tangentAt_wall (j : {j | x ∈ (D.wall j).support}) :
    (D.tangentAt x).wall j = (D.wall j.1).tangentAt x j.2 := (rfl)

/-- A wall through `x` is active in the tangent diagram exactly when it is active in the
diagram. -/
theorem mem_active_tangentAt (k : ℕ) (j : {j | x ∈ (D.wall j).support}) :
    j ∈ (D.tangentAt x).active k ↔ j.1 ∈ D.active k := by
  simp only [mem_active, tangentAt_wall, DirectedWall.tangentAt_label]

variable {x}

/-- Near `x`, an active wall of the diagram contains a point exactly when it passes through `x`
and the tangent wall contains the displacement. -/
theorem eventually_forall_mem_support_iff (k : ℕ) :
    ∀ᶠ y in 𝓝 x, ∀ j : D.active k, y ∈ (D.wall j).support ↔
      ∃ hj : x ∈ (D.wall j).support, y - x ∈ ((D.wall j).tangentAt x hj).support := by
  refine eventually_all.mpr fun j => ?_
  by_cases hj : x ∈ (D.wall j).support
  · filter_upwards [(D.wall j).eventually_mem_support_iff hj] with y hy
    exact ⟨fun h => ⟨hj, hy.mp h⟩, fun ⟨_, h⟩ => hy.mpr h⟩
  · filter_upwards [((D.wall j).isConvexPolyhedron.isClosed.isOpen_compl).mem_nhds hj] with y hy
    exact iff_of_false hy fun ⟨hj', _⟩ => hj hj'

/-- Near `x`, at a regular point of both diagrams, the combined label of the diagram in a
crossing direction is the combined label of the tangent diagram at the displacement from `x`.
Walls active at the cutoff but missing `x` contribute nothing, and repeated or coincident
indexed walls through `x` keep their separate factors. -/
theorem eventually_combinedLabel_tangentAt (k : ℕ) :
    ∀ᶠ y in 𝓝 x, ∀ (hy : y ∉ singularSupport (fun j : D.active k => (D.wall j).support))
      (hy' : y - x ∉ singularSupport (fun j : (D.tangentAt x).active k =>
        ((D.tangentAt x).wall j).support)) (v : V),
      D.combinedLabel k y v hy = (D.tangentAt x).combinedLabel k (y - x) v hy' := by
  classical
  filter_upwards [D.eventually_forall_mem_support_iff k] with y hyS hy hy' v
  let l : List ((D.tangentAt x).active k) :=
    (Set.toFinite {j : (D.tangentAt x).active k |
      y - x ∈ ((D.tangentAt x).wall j).support}).toFinset.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hm : ∀ j, j ∈ l ↔ y - x ∈ ((D.tangentAt x).wall j).support := by simp [l]
  let e : (D.tangentAt x).active k → D.active k := fun j =>
    ⟨j.1.1, (D.mem_active_tangentAt x k j.1).mp j.2⟩
  have he : Function.Injective e := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun j : D.active k => j.1) hab))
  rw [(D.tangentAt x).combinedLabel_eq_prod k (y - x) v hy' l hl hm,
    D.combinedLabel_eq_prod k y v hy (l.map e) (hl.map he) fun j => ?_]
  · rw [List.map_map]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, e, tangentAt_wall, DirectedWall.tangentAt_label,
      DirectedWall.tangentAt_normal]
  · rw [List.mem_map, hyS j]
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact ⟨j'.1.2, (hm j').mp hj'⟩
    · rintro ⟨hj, hjy⟩
      exact ⟨⟨⟨j.1, hj⟩, (D.mem_active_tangentAt x k ⟨j.1, hj⟩).mpr j.2⟩, (hm _).mpr hjy, rfl⟩

end Mei.DirectedDiagram
