/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Topology
public import Mei.Analysis.Convex.Polyhedron.Projection
public import Mei.Geometry.Affine.Segment
import Mathlib.Tactic.Linarith

/-!
# Stability of open segments with prescribed boundary contacts

Wall avoidance on an open segment persists under continuous variation when every
boundary contact stays in the wall's supporting hyperplane and the velocity there
is transverse. The analogous statement includes an unbounded incoming half-line.
The latter uses polyhedrality to exclude contacts escaping to infinity; the finite
segment only needs a closed wall.

These relative stability statements allow recorded encounters to remain on walls.
They complement the persistence of transverse interior contacts, and supply the
wall-avoidance part of closed endpoint-chart boundary analysis, following
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace ContinuousLinearMap

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]

/-- Avoidance on an open finite segment is stable relative to constraints fixing
any limiting endpoint contact in the supporting hyperplane. Such contacts must
be transverse. No convexity or polyhedrality of the closed wall is needed. -/
theorem eventually_forall_notMem_of_openSegment
    (ν : V →L[ℝ] ℝ) {c : ℝ} {W : Set V} (hW : IsClosed W)
    (hheight : ∀ y ∈ W, ν y = c) {v : V} {x : X → V} {b : X → ℝ}
    {Q : X} {D : Set X} (hx : ContinuousAt x Q) (hb : ContinuousAt b Q)
    (hpos : 0 < b Q)
    (havoid : ∀ t : ℝ, 0 < t → t < b Q → x Q + t • v ∉ W)
    (hstart : x Q ∈ W → ν v ≠ 0 ∧ ∀ Y ∈ D, ν (x Y) = c)
    (hend : x Q + b Q • v ∈ W →
      ν v ≠ 0 ∧ ∀ Y ∈ D, ν (x Y + b Y • v) = c) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D → ∀ t : ℝ, 0 < t → t < b Y → x Y + t • v ∉ W := by
  by_cases hv : ν v = 0
  · -- Tangent segments have no boundary contacts, so compact avoidance applies.
    have hall : ∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap (x Q) (x Q + b Q • v) t ∉ W := by
      intro t ht
      rw [AffineMap.lineMap_apply_module']
      simp only [add_sub_cancel_left, smul_smul]
      rw [add_comm]
      rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · simpa using fun h => (hstart h).1 hv
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · simpa using fun h => (hend h).1 hv
      · exact havoid _ (mul_pos ht0 hpos) (mul_lt_of_lt_one_left hpos ht1)
    have hp := (hx.prodMk (hx.add (hb.smul continuousAt_const))).eventually
      (hW.isOpen_setOf_lineMap_notMem.mem_nhds hall)
    filter_upwards [hp, continuousAt_const.eventually_lt hb hpos] with Y hY hYpos _ t ht ht'
    have he := hY (t / b Y) ⟨(div_pos ht hYpos).le, (div_lt_one hYpos).mpr ht' |>.le⟩
    simpa only [AffineMap.lineMap_apply_module', Pi.add_apply, Pi.smul_apply, Pi.smul_apply',
      add_sub_cancel_left, smul_smul,
      div_mul_cancel₀ _ hYpos.ne', add_comm] using he
  · -- For a transverse line the unique possible contact either misses the wall,
    -- stays outside the interval, or remains pinned to one of its ends.
    let r : X → ℝ := fun Y => (c - ν (x Y)) / ν v
    let p : X → V := fun Y => sweepProjection ν c ((ν v)⁻¹ • v) (x Y)
    have hr : ContinuousAt r Q :=
      (continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _
    have hp : ContinuousAt p Q := (sweepProjection ν c _).continuous.continuousAt.comp hx
    have hroot (Y : X) (t : ℝ) (ht : x Y + t • v ∈ W) : r Y = t := by
      apply (div_eq_iff hv).mpr
      have hh := hheight _ ht
      simp only [map_add, map_smul, smul_eq_mul] at hh
      linarith
    by_cases hpW : p Q ∈ W
    · have hformula : p Q = x Q + r Q • v := by
        simp only [p, r, sweepProjection_apply, smul_smul, div_eq_mul_inv]
      have hout : r Q ≤ 0 ∨ b Q ≤ r Q := by
        by_contra hn
        push Not at hn
        exact havoid _ hn.1 hn.2 (hformula ▸ hpW)
      rcases hout with hr0 | hbr
      · rcases eq_or_lt_of_le hr0 with he | he
        · have hs := (hstart (by simpa only [hformula, he, zero_smul, add_zero] using hpW)).2
          exact Eventually.of_forall fun Y hY t ht _ hmem => by
            have hh := hroot Y t hmem
            simp only [r, hs Y hY, sub_self, zero_div] at hh
            linarith
        · filter_upwards [hr.eventually_lt continuousAt_const he] with Y hY _ t ht _ hmem
          linarith [hroot Y t hmem]
      · rcases eq_or_lt_of_le hbr with he | he
        · have hs := (hend (by simpa only [hformula, ← he] using hpW)).2
          exact Eventually.of_forall fun Y hY t _ ht hmem => by
            have hh := hs Y hY
            have hh' := hheight _ hmem
            simp only [map_add, map_smul, smul_eq_mul] at hh hh'
            exact ht.ne (mul_right_cancel₀ hv (by linarith : t * ν v = b Y * ν v))
        · filter_upwards [hb.eventually_lt hr he] with Y hY _ t _ ht hmem
          linarith [hroot Y t hmem]
    · filter_upwards [hp.eventually (hW.isOpen_compl.mem_nhds hpW)] with Y hY _ t _ _ hmem
      apply hY
      simpa only [p, ν.sweepProjection_inv_smul_eq_add_smul hv (hheight _ hmem)] using hmem

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
    have hc := (isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem hW v).isClosed
    filter_upwards [hx.eventually (hc.isOpen_compl.mem_nhds hmiss)] with Y hY _ t ht
    exact fun hmem => hY ⟨t, ht.le, hmem⟩
  · -- A transverse ray has a unique possible contact, varying continuously.
    let r : X → ℝ := fun Y => (c - ν (x Y)) / ν v
    let p : X → V := fun Y => sweepProjection ν c ((ν v)⁻¹ • v) (x Y)
    have hr : ContinuousAt r Q :=
      (continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _
    have hp : ContinuousAt p Q := (sweepProjection ν c _).continuous.continuousAt.comp hx
    have hroot (Y : X) (t : ℝ) (ht : x Y + t • v ∈ W) : r Y = t := by
      apply (div_eq_iff hv).mpr
      have hh := hheight _ ht
      simp only [map_add, map_smul, smul_eq_mul] at hh
      linarith
    by_cases hpW : p Q ∈ W
    · have hformula : p Q = x Q + r Q • v := by
        simp only [p, r, sweepProjection_apply, smul_smul, div_eq_mul_inv]
      have hr0 : r Q ≤ 0 := le_of_not_gt fun ht => havoid _ ht (hformula ▸ hpW)
      rcases eq_or_lt_of_le hr0 with he | he
      · have hs := (hstart (by simpa only [hformula, he, zero_smul, add_zero] using hpW)).2
        exact Eventually.of_forall fun Y hY t ht hmem => by
          have hh := hroot Y t hmem
          simp only [r, hs Y hY, sub_self, zero_div] at hh
          linarith
      · filter_upwards [hr.eventually_lt continuousAt_const he] with Y hY _ t ht hmem
        linarith [hroot Y t hmem]
    · filter_upwards [hp.eventually (hW.isClosed.isOpen_compl.mem_nhds hpW)] with Y hY _ t _ hmem
      apply hY
      simpa only [p, ν.sweepProjection_inv_smul_eq_add_smul hv (hheight _ hmem)] using hmem

end ContinuousLinearMap
