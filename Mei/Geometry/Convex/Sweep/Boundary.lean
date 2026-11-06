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

open Set

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)

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
    f c v _ hdir hQ with ⟨j, ht⟩ | ⟨j, hj⟩
  · rcases backwardTime_eq_zero_imp_terminal_or_singularSupport f c v W wall
      hheight hclosed (Subset.refl _) hQ.1 j ht with hterminal | hsingular
    · exact Or.inl ⟨j, hterminal⟩
    · exact Or.inr ⟨j, hsingular⟩
  · exact Or.inr ⟨j, mem_singularSupport.mpr (Or.inl ⟨wall j, hj⟩)⟩

end Mei.Convex
