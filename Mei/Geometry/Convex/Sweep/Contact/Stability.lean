/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Polyhedron.Projection
public import Mei.Geometry.Affine.Segment
public import Mei.Geometry.Affine.Transverse
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

open Set Filter Topology

namespace ContinuousLinearMap

variable {V X : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [TopologicalSpace X]

/-- If the unique possible contact of a transverse line misses a closed wall,
nearby lines miss it entirely. -/
private theorem eventually_forall_notMem_of_contact_notMem
    (ν : V →L[ℝ] ℝ) {c : ℝ} {W : Set V} (hW : IsClosed W)
    (hheight : ∀ y ∈ W, ν y = c) {v : V} (hv : ν v ≠ 0) {x : X → V} {Q : X}
    (hx : ContinuousAt x Q) (hQ : x Q + ((c - ν (x Q)) / ν v) • v ∉ W) :
    ∀ᶠ Y in 𝓝 Q, ∀ t : ℝ, x Y + t • v ∉ W := by
  have hp : ContinuousAt (fun Y => x Y + ((c - ν (x Y)) / ν v) • v) Q :=
    hx.add (((continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _).smul
      continuousAt_const)
  filter_upwards [hp.eventually (hW.isOpen_compl.mem_nhds hQ)] with Y hY t hmem
  rw [ν.toLinearMap.eq_div_of_apply_add_smul_eq hv (hheight _ hmem)] at hmem
  exact hY hmem

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- If the contact parameter of a transverse line is negative, or is zero with the
base point pinned to the supporting hyperplane, nearby lines have no contact at a
positive time. -/
private theorem eventually_forall_pos_notMem_of_contact_nonpos
    (ν : V →L[ℝ] ℝ) {c : ℝ} {W : Set V} (hheight : ∀ y ∈ W, ν y = c) {v : V}
    (hv : ν v ≠ 0) {x : X → V} {Q : X} {D : Set X} (hx : ContinuousAt x Q)
    (hr : (c - ν (x Q)) / ν v ≤ 0)
    (hpin : (c - ν (x Q)) / ν v = 0 → ∀ Y ∈ D, ν (x Y) = c) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D → ∀ t : ℝ, 0 < t → x Y + t • v ∉ W := by
  rcases eq_or_lt_of_le hr with he | he
  · exact Eventually.of_forall fun Y hY t ht hmem => by
      have hh : t = (c - ν (x Y)) / ν v :=
        ν.toLinearMap.eq_div_of_apply_add_smul_eq hv (hheight _ hmem)
      simp only [hpin he Y hY, sub_self, zero_div] at hh
      linarith
  · have hr' : ContinuousAt (fun Y => (c - ν (x Y)) / ν v) Q :=
      (continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _
    filter_upwards [hr'.eventually_lt continuousAt_const he] with Y hY _ t ht hmem
    have hh : t = (c - ν (x Y)) / ν v :=
      ν.toLinearMap.eq_div_of_apply_add_smul_eq hv (hheight _ hmem)
    linarith

/-- Avoidance on an open finite segment is stable relative to constraints fixing
any limiting endpoint contact in the supporting hyperplane. Such contacts must
be transverse. The limiting segment may be collapsed. No convexity or polyhedrality of the
closed wall is needed. -/
theorem eventually_forall_notMem_of_openSegment
    (ν : V →L[ℝ] ℝ) {c : ℝ} {W : Set V} (hW : IsClosed W)
    (hheight : ∀ y ∈ W, ν y = c) {v : V} {x : X → V} {b : X → ℝ}
    {Q : X} {D : Set X} (hx : ContinuousAt x Q) (hb : ContinuousAt b Q)
    (havoid : ∀ t : ℝ, 0 < t → t < b Q → x Q + t • v ∉ W)
    (hstart : x Q ∈ W → ν v ≠ 0 ∧ ∀ Y ∈ D, ν (x Y) = c)
    (hend : x Q + b Q • v ∈ W →
      ν v ≠ 0 ∧ ∀ Y ∈ D, ν (x Y + b Y • v) = c) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D → ∀ t : ℝ, 0 < t → t < b Y → x Y + t • v ∉ W := by
  by_cases hv : ν v = 0
  · -- Tangent segments have no boundary contacts, so compact avoidance applies.
    rcases lt_or_ge (b Q) 0 with hneg | hnn
    · filter_upwards [hb.eventually_lt continuousAt_const hneg] with Y hY _ t ht ht'
      linarith
    have hall : ∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap (x Q) (x Q + b Q • v) t ∉ W := by
      intro t ht
      rcases eq_or_lt_of_le hnn with hb0 | hpos
      · simpa only [← hb0, zero_smul, add_zero, AffineMap.lineMap_same_apply] using
          fun h => (hstart h).1 hv
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
    filter_upwards [hp] with Y hY _ t ht ht'
    have hYpos : 0 < b Y := ht.trans ht'
    have he := hY (t / b Y) ⟨(div_pos ht hYpos).le, (div_lt_one hYpos).mpr ht' |>.le⟩
    simpa only [AffineMap.lineMap_apply_module', Pi.add_apply, Pi.smul_apply, Pi.smul_apply',
      add_sub_cancel_left, smul_smul,
      div_mul_cancel₀ _ hYpos.ne', add_comm] using he
  · -- For a transverse line the unique possible contact either misses the wall,
    -- stays outside the interval, or remains pinned to one of its ends.
    by_cases hpW : x Q + ((c - ν (x Q)) / ν v) • v ∈ W
    · have hout : (c - ν (x Q)) / ν v ≤ 0 ∨ b Q ≤ (c - ν (x Q)) / ν v := by
        by_contra hn
        push Not at hn
        exact havoid _ hn.1 hn.2 hpW
      rcases hout with hr0 | hbr
      · refine (eventually_forall_pos_notMem_of_contact_nonpos ν hheight hv hx hr0 fun he =>
          (hstart (by simpa only [he, zero_smul, add_zero] using hpW)).2).mono ?_
        exact fun Y h hY t ht _ => h hY t ht
      · rcases eq_or_lt_of_le hbr with he | he
        · have hs := (hend (by simpa only [← he] using hpW)).2
          exact Eventually.of_forall fun Y hY t _ ht hmem => by
            have hh := hs Y hY
            have hh' := hheight _ hmem
            simp only [map_add, map_smul, smul_eq_mul] at hh hh'
            exact ht.ne (mul_right_cancel₀ hv (by linarith : t * ν v = b Y * ν v))
        · have hr : ContinuousAt (fun Y => (c - ν (x Y)) / ν v) Q :=
            (continuousAt_const.sub (ν.continuous.continuousAt.comp hx)).div_const _
          filter_upwards [hb.eventually_lt hr he] with Y hY _ t _ ht hmem
          have hh : t = (c - ν (x Y)) / ν v :=
            ν.toLinearMap.eq_div_of_apply_add_smul_eq hv (hheight _ hmem)
          linarith
    · filter_upwards [eventually_forall_notMem_of_contact_notMem ν hW hheight hv hx hpW]
        with Y hY _ t _ _
      exact hY t

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
