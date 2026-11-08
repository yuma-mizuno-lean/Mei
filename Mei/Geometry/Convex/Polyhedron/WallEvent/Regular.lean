/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.WallEvent

/-!
# Regular limits of exact simultaneous events

An exact event support need not be closed: a limit can acquire additional wall
indices. For closed ambient walls this can happen only in singular support.
At a regular limit the entire incidence set persists, and the event support
agrees locally with any of its recorded walls. Thus replacing selected closed
walls by exact simultaneous events introduces no new regular boundary events.

The argument uses relative-interior neighborhoods and the equality of the
affine spans of walls meeting at a regular point. No polyhedral, codimension
or finite-dimensional hypothesis is needed. The simultaneous-event convention
is that of `WallEvent.support`, retaining coincident indexed walls separately.
-/

public section

open Set Filter Topology

namespace Mei.Convex.WallEvent

variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (e : WallEvent ι) (W : ι → Set V) (hclosed : ∀ j, IsClosed (W j))

include hclosed

/-- A regular limit of an exact event retains every recorded and omitted wall
index. Closedness of the ambient walls suffices even for an infinite alphabet. -/
theorem mem_support_of_mem_closure {x : V} (hx : x ∈ closure (e.support W))
    (hregular : x ∉ singularSupport W) : x ∈ e.support W := by
  have hrecorded (j : ι) (hj : j ∈ e.1.val) : x ∈ W j :=
    closure_minimal (e.support_subset W hj) (hclosed j) hx
  have hx₀ := hrecorded _ e.1.property.choose_spec
  apply (e.mem_support W x).mpr
  intro j
  refine ⟨fun hxj => ?_, hrecorded j⟩
  by_contra hj
  have hspan := affineSpan_eq_of_notMem_singularSupport hregular hxj hx₀
  have hnear := Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior
    (mem_intrinsicInterior_of_notMem_singularSupport hxj hregular)
  rw [hspan, mem_nhdsWithin_iff_eventually] at hnear
  obtain ⟨y, hy, hynear⟩ := ((mem_closure_iff_frequently.mp hx).and_eventually hnear).exists
  exact hj (((e.mem_support W y).mp hy j).mp (hynear (subset_affineSpan ℝ _
    (e.support_subset W e.1.property.choose_spec hy))))

variable [Finite ι]

/-- Near a regular event point, its exact incidence support agrees with any
recorded ambient wall. The crossing sign does not affect this geometric germ. -/
theorem eventually_mem_support_iff {x : V} (hx : x ∈ e.support W)
    (hregular : x ∉ singularSupport W) {j : ι} (hj : j ∈ e.1.val) :
    ∀ᶠ y in 𝓝 x, y ∈ e.support W ↔ y ∈ W j := by
  have hxj := e.support_subset W hj hx
  have hS (k : ι) (hxk : x ∈ W k) :
      (affineSpan ℝ (W j)).direction ≤ (affineSpan ℝ (W k)).direction := by
    rw [affineSpan_eq_of_notMem_singularSupport hregular hxj hxk]
  have hdisp := Mei.Convex.eventually_mem_iff_of_submodule_le_direction W hclosed x hregular
    (affineSpan ℝ (W j)).direction hS
  rw [nhds_subtype, Submodule.coe_zero, eventually_comap] at hdisp
  have ht : Tendsto (fun y : V => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  filter_upwards [ht.eventually hdisp] with y hy
  refine ⟨fun hy => e.support_subset W hj hy, fun hyj => (e.mem_support W y).mpr (fun k => ?_)⟩
  have hyk := hy ⟨y - x, AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ _ hyj) (subset_affineSpan ℝ _ hxj)⟩ rfl k
  simp only [add_sub_cancel] at hyk
  exact hyk.trans ((e.mem_support W x).mp hx k)

/-- Even at a limit of a nonclosed exact support, its regular germ is the germ
of each recorded wall. This includes all coincident wall indices. -/
theorem eventually_mem_support_iff_of_mem_closure {x : V}
    (hx : x ∈ closure (e.support W)) (hregular : x ∉ singularSupport W)
    {j : ι} (hj : j ∈ e.1.val) :
    ∀ᶠ y in 𝓝 x, y ∈ e.support W ↔ y ∈ W j :=
  e.eventually_mem_support_iff W hclosed
    (e.mem_support_of_mem_closure W hclosed hx hregular) hregular hj

end Mei.Convex.WallEvent
