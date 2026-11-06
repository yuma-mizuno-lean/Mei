/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Polyhedron.Projection
public import Mei.Geometry.Affine.Segment
import Mathlib.Tactic.Linarith

/-!
# Stability of open rays with prescribed boundary contacts

Wall avoidance on an open incoming half-line persists under continuous variation
when a boundary contact stays in the wall's supporting hyperplane and the velocity
there is transverse. Polyhedrality excludes contacts escaping to infinity. The
finite-segment counterpart is in `Mei.Geometry.Affine.Segment` and only needs a
closed wall.

These relative stability statements allow recorded encounters to remain on walls.
They complement the persistence of transverse interior contacts, and supply the
wall-avoidance part of closed endpoint-chart boundary analysis, following
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace ContinuousLinearMap

variable {V X : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [TopologicalSpace X]

/-- Avoidance on an open incoming half-line is stable relative to constraints
fixing a limiting base contact in its supporting hyperplane. Polyhedrality
excludes contacts escaping to infinity, including for tangent or zero velocity. -/
theorem eventually_forall_notMem_of_openRay
    (ν : V →L[ℝ] ℝ) {c : ℝ} {W : Set V} (hW : TauCeti.IsConvexPolyhedron W)
    (hheight : ∀ y ∈ W, ν y = c) {v : V} {x : X → V}
    {Q : X} {D : Set X} (hx : ContinuousAt x Q)
    (havoid : ∀ t : ℝ, 0 < t → x Q + t • v ∉ W)
    (hstart : x Q ∈ W → ν v ≠ 0 ∧ ∀ Y ∈ D, ν (x Y) = c) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D → ∀ t : ℝ, 0 < t → x Y + t • v ∉ W := by
  by_cases hv : ν v = 0
  · -- A tangent ray misses the wall even at its base; its closed sweep is closed.
    have hmiss : x Q ∉ {y | ∃ t : ℝ, 0 ≤ t ∧ y + t • v ∈ W} := by
      rintro ⟨t, ht, hmem⟩
      rcases eq_or_lt_of_le ht with rfl | ht
      · exact (hstart (by simpa using hmem)).1 hv
      · exact havoid t ht hmem
    have hc := (Mei.Convex.isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem hW v).isClosed
    filter_upwards [hx.eventually (hc.isOpen_compl.mem_nhds hmiss)] with Y hY _ t ht
    exact fun hmem => hY ⟨t, ht.le, hmem⟩
  · -- A transverse ray has a unique possible contact, varying continuously.
    by_cases hpW : x Q + ((c - ν (x Q)) / ν v) • v ∈ W
    · exact eventually_forall_pos_notMem_of_contact_nonpos ν hheight hv hx
        (le_of_not_gt fun ht => havoid _ ht hpW) fun he =>
          (hstart (by simpa only [he, zero_smul, add_zero] using hpW)).2
    · filter_upwards [eventually_forall_notMem_of_contact_notMem ν hW.isClosed hheight hv hx hpW]
        with Y hY _ t _
      exact hY t

end ContinuousLinearMap
