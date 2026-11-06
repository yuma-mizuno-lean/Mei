/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Analysis.Convex.Intrinsic
public import Mei.Geometry.Convex.Polyhedron.Rational.Tangent

/-!
# Tangent walls at a point of the support

At a point `x` of the support of a directed wall, the tangent wall replaces the support by
its tangent cone at `x`, a rational-normal cone with zero offset, and keeps the normal,
the supported ray and the label. Near `x` the wall and the translate of the tangent wall by
`x` have the same points. The tangent wall has the same spatial velocity. A wall which is
incoming stays incoming, while an outgoing wall may become incoming, as happens at a vertex
of a bounded support.

This is the wall-level step of passing from a diagram to the diagram of the walls through a
joint, whose supports are cones. No lattice rationality of `x` and no full-hyperplane
hypothesis is needed; the support may be bounded or have lineality.
-/

public section

noncomputable section

open Set Filter Topology

namespace Mei

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

namespace DirectedWall

variable (W : DirectedWall (d := d) h H) {x : V}

/-- The tangent wall at a point of the support: the support becomes its tangent cone at
that point, and all other data are unchanged. -/
def tangentAt (W : DirectedWall (d := d) h H) (x : V) (hx : x ∈ W.support) :
    DirectedWall (d := d) h H where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := posTangentConeAt W.support x
  support_nonempty := ⟨0, by
    simpa using W.isConvexPolyhedron.convex.sub_mem_posTangentConeAt hx hx⟩
  rational_support := W.rational_support.posTangentConeAt hx
  direction_support := by
    have := h.finiteDimensional
    rw [W.isConvexPolyhedron.convex.direction_affineSpan_posTangentConeAt hx,
      W.direction_support]
  label := W.label
  label_mem := W.label_mem

/-- The support of the tangent wall is the tangent cone of the support. -/
@[simp]
theorem tangentAt_support (hx : x ∈ W.support) :
    (W.tangentAt x hx).support = posTangentConeAt W.support x := (rfl)

/-- The tangent wall has the normal of the wall. -/
@[simp]
theorem tangentAt_normal (hx : x ∈ W.support) : (W.tangentAt x hx).normal = W.normal := (rfl)

/-- The tangent wall has the supported ray of the wall. -/
@[simp]
theorem tangentAt_ray (hx : x ∈ W.support) : (W.tangentAt x hx).ray = W.ray := (rfl)

/-- The tangent wall has the label of the wall. -/
@[simp]
theorem tangentAt_label (hx : x ∈ W.support) : (W.tangentAt x hx).label = W.label := (rfl)

/-- The tangent wall has the spatial velocity of the wall. -/
@[simp]
theorem tangentAt_direction (hx : x ∈ W.support) : (W.tangentAt x hx).direction = W.direction := by
  rw [direction_def, direction_def, tangentAt_ray]

/-- Displacements from `x` to points of the support are supported by the tangent wall. -/
theorem sub_mem_tangentAt_support (hx : x ∈ W.support) {y : V} (hy : y ∈ W.support) :
    y - x ∈ (W.tangentAt x hx).support :=
  W.isConvexPolyhedron.convex.sub_mem_posTangentConeAt hx hy

/-- The origin lies in the support of the tangent wall. -/
theorem zero_mem_tangentAt_support (hx : x ∈ W.support) : (0 : V) ∈ (W.tangentAt x hx).support := by
  simpa using W.sub_mem_tangentAt_support hx hx

/-- The tangent wall is a cone: its support is invariant under nonnegative scaling. -/
theorem smul_mem_tangentAt_support (hx : x ∈ W.support) {v : V}
    (hv : v ∈ (W.tangentAt x hx).support) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ (W.tangentAt x hx).support :=
  W.rational_support.smul_mem_posTangentConeAt hx hv ht

/-- Near `x`, a point lies in the support exactly when its displacement from `x` lies in the
support of the tangent wall. -/
theorem eventually_mem_support_iff (hx : x ∈ W.support) :
    ∀ᶠ y in 𝓝 x, y ∈ W.support ↔ y - x ∈ (W.tangentAt x hx).support :=
  W.rational_support.eventually_mem_iff_sub_mem_posTangentConeAt hx

/-- An incoming wall has an incoming tangent wall at each point of its support. A wall that is
outgoing may have an incoming tangent wall. -/
theorem Incoming.tangentAt (hW : W.Incoming) (hx : x ∈ W.support) :
    (W.tangentAt x hx).Incoming := by
  rw [(W.tangentAt x hx).incoming_iff, tangentAt_ray]
  intro y hy t ht
  have hw : i (ρ W.ray.generator) ∈ (W.tangentAt x hx).support := by
    have := W.sub_mem_tangentAt_support hx (W.incoming_iff.mp hW x hx 1 zero_le_one)
    simpa using this
  exact W.rational_support.add_mem_posTangentConeAt hx hy
    (W.smul_mem_tangentAt_support hx hw ht)

/-- At a relative interior point of the support, the tangent wall is the full supporting
hyperplane through the origin. -/
theorem tangentAt_support_eq_ker (hx : x ∈ intrinsicInterior ℝ W.support) :
    (W.tangentAt x (intrinsicInterior_subset hx)).support =
      LinearMap.ker (h.realCharacter W.normal) := by
  have := h.finiteDimensional
  have hxs := intrinsicInterior_subset hx
  ext v
  rw [tangentAt_support, SetLike.mem_coe, ← W.direction_support]
  refine ⟨fun hv => posTangentConeAt_subset_direction_affineSpan hxs hv, fun hv => ?_⟩
  have hline : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝[affineSpan ℝ W.support] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact Eventually.of_forall fun t => by
        simpa [add_comm] using (affineSpan ℝ W.support).vadd_mem_of_mem_direction
          ((affineSpan ℝ W.support).direction.smul_mem t hv) (subset_affineSpan ℝ _ hxs)
  obtain ⟨t, ht, htpos⟩ := ((hline.eventually
    (mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hx)).and self_mem_nhdsWithin).exists
  have hsub := W.sub_mem_tangentAt_support hxs ht
  rw [add_sub_cancel_left] at hsub
  simpa [smul_smul, htpos.ne'] using W.smul_mem_tangentAt_support hxs hsub (inv_nonneg.mpr htpos.le)

end DirectedWall

end Mei
