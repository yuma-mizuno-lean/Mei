/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Square meshes subordinate to convex open covers

A continuous map on the closed unit square admits a finite uniform square mesh
whose cells lie in members of any given convex open cover of its image. A single
positive radius works for perturbing every image point before taking convex hulls.
In particular, one can move mesh vertices and interpolate their new values by
affine triangles while retaining containment in the same cover members.

The construction uses Mathlib's metric Lebesgue number lemma and Heine--Cantor
theorem. Neither the map nor its image needs to be injective.
-/

public section

open Set Metric

namespace Mei

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [PseudoMetricSpace V]

/-- A continuous square has a uniform mesh subordinate to a convex open cover.
Each entire cell image, thickened by a common positive radius and then convexified,
lies in one cover member. Thus the conclusion also controls arbitrary finite
affine interpolations of perturbed vertex values. -/
theorem exists_square_mesh_convexHull_ball_subset
    (H : ℝ × ℝ → V)
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (U : ι → Set V) (hopen : ∀ j, IsOpen (U j)) (hconvex : ∀ j, Convex ℝ (U j))
    (hcover : H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ ⋃ j, U j) :
    ∃ n : ℕ, 0 < n ∧ ∃ ε > 0, ∀ a b : Fin n, ∃ j,
      convexHull ℝ (⋃ z ∈
        (Icc ((a : ℝ) / n) (((a : ℝ) + 1) / n) ×ˢ
          Icc ((b : ℝ) / n) (((b : ℝ) + 1) / n)), ball (H z) ε) ⊆ U j := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, hlocal⟩ := lebesgue_number_lemma_of_metric
    (hcompact.image_of_continuousOn hH) hopen hcover
  obtain ⟨η, hη, hsmall⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hH) (δ / 2) (half_pos hδ)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : (1 : ℝ) / n < η := by simpa only [n, Nat.cast_add, Nat.cast_one] using hm
  have hcoord (a : Fin n) :
      0 ≤ (a : ℝ) / n ∧ ((a : ℝ) + 1) / n ≤ 1 := by
    have ha : (a : ℝ) + 1 ≤ n := by exact_mod_cast a.isLt
    exact ⟨div_nonneg (Nat.cast_nonneg _) hnreal.le, (div_le_one hnreal).mpr ha⟩
  have hleft (c : Fin n) : (c : ℝ) / n ∈ Icc ((c : ℝ) / n) (((c : ℝ) + 1) / n) :=
    left_mem_Icc.mpr (by gcongr; linarith)
  refine ⟨n, hn, δ / 2, half_pos hδ, fun a b => ?_⟩
  have hcell : Icc ((a : ℝ) / n) (((a : ℝ) + 1) / n) ×ˢ Icc ((b : ℝ) / n) (((b : ℝ) + 1) / n) ⊆
      Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (Icc_subset_Icc (hcoord a).1 (hcoord a).2)
      (Icc_subset_Icc (hcoord b).1 (hcoord b).2)
  let p : ℝ × ℝ := ((a : ℝ) / n, (b : ℝ) / n)
  have hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := hcell ⟨hleft a, hleft b⟩
  obtain ⟨j, hj⟩ := hlocal (H p) (mem_image_of_mem H hp)
  refine ⟨j, convexHull_min ?_ (hconvex j)⟩
  intro y hy
  obtain ⟨z, hzcell, hy⟩ := mem_iUnion₂.mp hy
  have hzsquare : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := hcell hzcell
  have hdistcoord (c : Fin n) (t : ℝ)
      (ht : t ∈ Icc ((c : ℝ) / n) (((c : ℝ) + 1) / n)) :
      dist t ((c : ℝ) / n) ≤ 1 / n := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2, add_div (c : ℝ) 1 (n : ℝ)]
  have hzdist : dist z p < η := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(hdistcoord a z.1 hzcell.1).trans_lt hstep,
      (hdistcoord b z.2 hzcell.2).trans_lt hstep⟩
  have hHz := hsmall z hzsquare p hp hzdist
  have hyz : dist y (H z) < δ / 2 := mem_ball.mp hy
  exact hj (mem_ball.mpr ((dist_triangle y (H z) (H p)).trans_lt (by linarith)))

end Mei
