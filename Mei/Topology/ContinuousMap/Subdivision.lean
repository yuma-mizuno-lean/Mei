/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.ContinuousMap.Subdivision
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Subdivisions stable under vertex perturbations

A continuous square filling admits a grid subordinate to an open cover, with
one positive perturbation bound for all cells. The same member of the cover
contains the entire original patch and the convex hull of its four perturbed
vertices. This allows subsequent choices of admissible polygonal edges while
retaining local control of the filling.

This extends `ContinuousMap.exists_grid_subdivision` from Tau Ceti. A metric
Lebesgue number and a refinement by smaller balls provide the extra room for
perturbations; convexity of balls controls the resulting polygonal patches.
-/

public section

open Set
open scoped unitInterval

namespace ContinuousMap

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Subdivide a square filling under an open cover, retaining a uniform positive
margin for perturbing its vertices. Each cover member contains both the whole
original parameter patch and the convex hull of its four perturbed corners.
The grid times start at zero, are monotone, and reach one at the final index. -/
theorem exists_grid_subdivision_convexHull (f : C(↥unitInterval × ↥unitInterval, V))
    (U : ι → Set V) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, f x ∈ U j) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
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
  obtain ⟨m, t, ht0, hmono, htail, hgrid⟩ := f.exists_grid_subdivision
    (fun x => Metric.ball (f x) (δ / 3)) (fun _ => Metric.isOpen_ball)
    (fun x => ⟨x, Metric.mem_ball_self (by positivity)⟩)
  refine ⟨m + 1, t, by omega, ht0, hmono, htail _ (by omega),
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
