/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Collision

/-!
# Boundaries of selected wall incidences

A backward itinerary with positive elapsed times and encounters in the relative
interiors of its selected walls persists under small changes of endpoint. Each
wall must span its prescribed supporting hyperplane. The propagation maps can
have smaller rank after earlier encounters; their continuity into the supporting
hyperplanes suffices, with no surjectivity assumption.

Consequently a boundary endpoint of the selected-incidence domain has a zero
elapsed time or an encounter on a relative wall boundary. Combining this with
the collision theorem, every such boundary is terminal or singular. These are
the support and time constraints only: incoming-source admission and avoidance
of unrecorded walls impose additional conditions.

We use relative-interior neighborhoods in affine spans and the existing
`backwardTime_eq_zero_imp_terminal_or_singularSupport`. The interpretation as
degenerations of endpoint charts follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)
  (P : Fin n → Set V)
  (hheight : ∀ j x, x ∈ P j → f j x = c j)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (P j)).direction)

include hheight hdir

/-- Strict time order and relative-interior wall encounters persist near the
endpoint. No convexity, closedness or finite-dimensionality is required. -/
theorem mem_interior_backwardDomain {Q : V}
    (ht : ∀ j, 0 < backwardTime f c v j Q)
    (hP : ∀ j, backwardPoint f c v j.succ Q ∈ intrinsicInterior ℝ (P j)) :
    Q ∈ interior (backwardDomain f c v P) := by
  apply mem_interior_iff_mem_nhds.mpr
  suffices he : ∀ᶠ X in 𝓝 Q, ∀ j,
      0 < backwardTime f c v j X ∧ backwardPoint f c v j.succ X ∈ P j by
    exact he.mono fun X hX => (mem_backwardDomain f c v P X).mpr hX
  apply eventually_all.mpr
  intro j
  have hf : f j (v j) ≠ 0 := by
    intro hz
    have htj := ht j
    simp only [backwardTime_apply, hz, div_zero] at htj
    exact (lt_irrefl 0) htj
  have hspan (X : V) : backwardPoint f c v j.succ X ∈ affineSpan ℝ (P j) := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem
      (subset_affineSpan ℝ _ (intrinsicInterior_subset (hP j)))]
    apply hdir j
    rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
    simp only [ContinuousLinearMap.coe_coe]
    rw [backwardPoint_height f c v j hf X,
      hheight j _ (intrinsicInterior_subset (hP j)), sub_self]
  have hlim := tendsto_nhdsWithin_iff.mpr
    ⟨(backwardPoint f c v j.succ).continuous.tendsto Q, Eventually.of_forall hspan⟩
  exact ((backwardTime f c v j).continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (ht j))).and
      (hlim.eventually (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior (hP j)))

/-- At a boundary of the selected-incidence domain, some elapsed time vanishes
or a selected encounter lies on its wall's relative boundary. The converse can
fail when an encounter map has smaller rank. -/
theorem mem_frontier_backwardDomain_imp_time_eq_zero_or_mem_intrinsicFrontier
    (hclosed : ∀ j, IsClosed (P j)) {Q : V}
    (hQ : Q ∈ frontier (backwardDomain f c v P)) :
    (∃ j, backwardTime f c v j Q = 0) ∨
      ∃ j, backwardPoint f c v j.succ Q ∈ intrinsicFrontier ℝ (P j) := by
  have hw := closure_minimal (backwardDomain_subset_weakBackwardDomain f c v P)
    (isClosed_weakBackwardDomain f c v hclosed) hQ.1
  have hm := (mem_weakBackwardDomain f c v P Q).mp hw
  by_contra! hnone
  have ht (j) : 0 < backwardTime f c v j Q :=
    lt_of_le_of_ne (hm j).1 (Ne.symm (hnone.1 j))
  have hi (j) : backwardPoint f c v j.succ Q ∈ intrinsicInterior ℝ (P j) := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    exact ⟨subset_intrinsicClosure (hm j).2, hnone.2 j⟩
  exact hQ.2 (mem_interior_backwardDomain f c v P hheight hdir ht hi)

omit hheight hdir

variable {ι : Type*} (W : ι → Set V) (wall : Fin n → ι)

/-- A selected-incidence boundary is a terminal wall encounter or an encounter
in singular support. Repeated and coincident indexed walls are allowed. -/
theorem mem_frontier_backwardDomain_imp_terminal_or_singularSupport
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤
      (affineSpan ℝ (W (wall j))).direction)
    (hclosed : ∀ j, IsClosed (W j)) {Q : V}
    (hQ : Q ∈ frontier (backwardDomain f c v (fun j => W (wall j)))) :
    (∃ j : Fin n, j.val = 0 ∧ Q ∈ W (wall j)) ∨
      ∃ j : Fin n, backwardPoint f c v j.succ Q ∈ singularSupport W := by
  rcases mem_frontier_backwardDomain_imp_time_eq_zero_or_mem_intrinsicFrontier
    f c v _ hheight hdir (fun j => hclosed (wall j)) hQ with ⟨j, ht⟩ | ⟨j, hj⟩
  · rcases backwardTime_eq_zero_imp_terminal_or_singularSupport f c v W wall
      hheight hclosed (Subset.refl _) hQ.1 j ht with hterminal | hsingular
    · exact Or.inl ⟨j, hterminal⟩
    · exact Or.inr ⟨j, hsingular⟩
  · exact Or.inr ⟨j, mem_singularSupport.mpr (Or.inl ⟨wall j, hj⟩)⟩

end Mei.Convex
