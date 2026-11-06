/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Tangent
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Singular support of tangent polyhedral families

Near a point, a finite polyhedral family agrees with the translated tangent cones of
the members through that point. This comparison includes relative boundaries and
intersections of different supporting directions, hence the actual singular support.
It allows regularity to be compared when shrinking paths towards the base point.
Empty, bounded, coincident and non-full-dimensional members are allowed.

The argument uses `Convex.direction_affineSpan_posTangentConeAt` to retain the relative
topology of each support, and the local carrier comparison for convex polyhedra.
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  (W : ι → Set V) (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j)) (x : V)

include hW

variable [FiniteDimensional ℝ V]

/-- The actual singular support near the base point is the translate of the singular
support of the tangent cones of precisely the members containing that point. -/
theorem eventually_mem_singularSupport_iff_sub_mem_posTangentConeAt :
    ∀ᶠ y in 𝓝 x, y ∈ singularSupport W ↔
      y - x ∈ singularSupport (fun j : {j | x ∈ W j} => posTangentConeAt (W j) x) := by
  have hfront : ∀ᶠ y in 𝓝 x, ∀ j, y ∈ intrinsicFrontier ℝ (W j) ↔
      ∃ _ : x ∈ W j, y - x ∈ intrinsicFrontier ℝ (posTangentConeAt (W j) x) := by
    refine eventually_all.mpr fun j => ?_
    by_cases hj : x ∈ W j
    · filter_upwards [(hW j).eventually_mem_intrinsicFrontier_iff_sub_mem_posTangentConeAt hj]
        with y hy
      exact ⟨fun h => ⟨hj, hy.mp h⟩, fun ⟨_, h⟩ => hy.mpr h⟩
    · filter_upwards [(hW j).isClosed.isOpen_compl.mem_nhds hj] with y hy
      exact iff_of_false (fun hf => hy (intrinsicFrontier_subset (hW j).isClosed hf))
        (fun ⟨hj', _⟩ => hj hj')
  filter_upwards [eventually_forall_mem_iff_sub_mem_posTangentConeAt W hW x, hfront]
    with y hy hyfront
  simp only [mem_singularSupport]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, l, hne, hj, hl⟩)
    · obtain ⟨hjx, hj⟩ := (hyfront j).mp hj
      exact Or.inl ⟨⟨j, hjx⟩, hj⟩
    · obtain ⟨hjx, hj⟩ := (hy j).mp hj
      obtain ⟨hlx, hl⟩ := (hy l).mp hl
      exact Or.inr ⟨⟨j, hjx⟩, ⟨l, hlx⟩, by
        simpa only [(hW j).convex.direction_affineSpan_posTangentConeAt hjx,
          (hW l).convex.direction_affineSpan_posTangentConeAt hlx] using hne, hj, hl⟩
  · rintro (⟨⟨j, hjx⟩, hj⟩ | ⟨⟨j, hjx⟩, ⟨l, hlx⟩, hne, hj, hl⟩)
    · exact Or.inl ⟨j, (hyfront j).mpr ⟨hjx, hj⟩⟩
    · exact Or.inr ⟨j, l, by
        simpa only [(hW j).convex.direction_affineSpan_posTangentConeAt hjx,
          (hW l).convex.direction_affineSpan_posTangentConeAt hlx] using hne,
        (hy j).mpr ⟨hjx, hj⟩, (hy l).mpr ⟨hlx, hl⟩⟩

end Mei.Convex
