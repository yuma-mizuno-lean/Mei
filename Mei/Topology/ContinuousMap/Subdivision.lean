/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mei.Topology.UnitInterval

/-!
# Subdivisions stable under vertex perturbations

A continuous square filling admits a grid subordinate to an open cover, with
one positive perturbation bound for all cells. The same member of the cover
contains the entire original patch and the convex hull of its four perturbed
vertices. This allows subsequent choices of admissible polygonal edges while
retaining local control of the filling.

The mesh construction adapts Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`
(Patrick Massot and Kim Morrison, Apache 2.0), choosing its step
with `Set.Countable.exists_pos_addNSMul_notMem`. This extends
`ContinuousMap.exists_grid_subdivision` from Tau Ceti. A metric
Lebesgue number and a refinement by smaller balls provide the extra room for
perturbations; convexity of balls controls the resulting polygonal patches.
-/

public section

open Set
open scoped unitInterval

namespace ContinuousMap

/-- Subdivide a continuous square under an open cover, choosing every mesh time
outside a countable exceptional set. The endpoints must avoid that set. -/
theorem exists_grid_subdivision_avoiding {X : Type*} {ι : Sort*} [TopologicalSpace X]
    (f : C(↥unitInterval × ↥unitInterval, X))
    (U : ι → Set X) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, f x ∈ U j)
    (S : Set ℝ) (hS : S.Countable) (h0 : 0 ∉ S) (h1 : 1 ∉ S) :
    ∃ (m : ℕ) (t : ℕ → unitInterval), t 0 = 0 ∧ Monotone t ∧
      (∀ n, m ≤ n → t n = 1) ∧ (∀ n, (t n : ℝ) ∉ S) ∧
      ∀ a b, ∃ j, MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (U j) := by
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun j => (hU j).preimage f.continuous) (by
      intro x _
      exact mem_iUnion.mpr (hcover x))
  obtain ⟨δ, hδ, havoid⟩ := hS.exists_pos_addNSMul_notMem h0 h1 hε
  let t := Icc.addNSMul (zero_le_one : (0 : ℝ) ≤ 1) δ
  obtain ⟨m, hm⟩ := Icc.addNSMul_eq_right (zero_le_one : (0 : ℝ) ≤ 1) hδ.1
  refine ⟨m, t, Subtype.ext (Icc.addNSMul_zero _),
    Icc.monotone_addNSMul _ hδ.1.le, fun n hn => Subtype.ext (hm n hn),
    havoid, fun a b => ?_⟩
  obtain ⟨j, hj⟩ := hball (t a, t b) (mem_univ _)
  refine ⟨j, fun x hx => hj ?_⟩
  exact Metric.mem_ball.mpr ((max_le
    (Icc.abs_sub_addNSMul_le _ hδ.1.le a hx.1)
    (Icc.abs_sub_addNSMul_le _ hδ.1.le b hx.2)).trans_lt hδ.2)

variable {V : Type*} {ι : Sort*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Subdivide a square filling under an open cover, retaining a uniform positive
margin for perturbing its vertices. For each grid cell, one cover member contains
both its entire image patch and the convex hull of its four perturbed corners.
The grid times start at zero, are monotone, and reach one at the final index.
They avoid the prescribed countable exceptional set missing the endpoints. -/
theorem exists_grid_subdivision_convexHull (f : C(↥unitInterval × ↥unitInterval, V))
    (U : ι → Set V) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, f x ∈ U j)
    (S : Set ℝ) (hS : S.Countable) (h0 : 0 ∉ S) (h1 : 1 ∉ S) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      (∀ a, (t a : ℝ) ∉ S) ∧
      ∃ ε > 0, ∀ a b : Fin n, ∃ j,
        MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (U j) ∧
        ∀ v : Fin 2 × Fin 2 → V,
          (∀ e, dist (v e) (f (t (a + e.1.val), t (b + e.2.val))) < ε) →
          convexHull ℝ (range v) ⊆ U j := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_range f.continuous) hU (by
      rintro _ ⟨x, rfl⟩
      exact mem_iUnion.mpr (hcover x))
  -- Refine by small balls before using the existing square subdivision.
  obtain ⟨m, t, ht0, hmono, htail, havoid, hgrid⟩ := f.exists_grid_subdivision_avoiding
    (fun x => Metric.ball (f x) (δ / 3)) (fun _ => Metric.isOpen_ball)
    (fun x => ⟨x, Metric.mem_ball_self (by positivity)⟩) S hS h0 h1
  refine ⟨m + 1, t, by omega, ht0, hmono, htail _ (by omega), havoid,
    δ / 3, by positivity, fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hgrid a b
  obtain ⟨j, hj⟩ := hball (f x) (mem_range_self x)
  refine ⟨j, fun y hy => hj (Metric.ball_subset_ball
    (by linarith : δ / 3 ≤ δ) (hx hy)), fun v hv => ?_⟩
  -- Every perturbed corner stays in the larger ball; its hull stays there too.
  apply (convexHull_min (t := Metric.ball (f x) δ) ?_ (convex_ball _ _)).trans hj
  rintro _ ⟨e, rfl⟩
  have hcorner (c : ℕ) (k : Fin 2) : t (c + k.val) ∈ Icc (t c) (t (c + 1)) :=
    ⟨hmono (by omega), hmono (by omega)⟩
  have hc : dist (f (t (a + e.1.val), t (b + e.2.val))) (f x) < δ / 3 :=
    hx ⟨hcorner a e.1, hcorner b e.2⟩
  exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith [hv e])

end ContinuousMap
