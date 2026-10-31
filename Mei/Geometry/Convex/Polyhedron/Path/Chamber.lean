/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mei.Topology.Connected.Adjacency

/-!
# Chambers of allowed endpoints

The chambers of a wall family are the connected components of the complement of
all walls, with the topology induced from the ambient space. Every allowed
endpoint of an admissible path determines its chamber. Points of one preconnected
wall-free set lie in one chamber; in particular a segment meeting no wall joins
two points of the same chamber.

Chambers are Mathlib's `ConnectedComponents` of the complement. Their ambient
carriers are `ConnectedComponents.carrier`, so membership of a point that is not
itself an allowed endpoint can be stated without choosing a proof that it avoids the
walls. No closedness, finiteness or local finiteness of the walls is needed.
-/

public section

open Set

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] {W : ι → Set V}

/-- The chambers of a wall family: the connected components of the complement of
all walls, with the subspace topology. -/
abbrev Chamber (W : ι → Set V) := ConnectedComponents {x : V | ∀ i, x ∉ W i}

/-- The chamber containing an allowed endpoint. -/
def chamber (x : WallComplement W) : Chamber W :=
  ConnectedComponents.mk ⟨x.val, x.notMem⟩

/-- An allowed endpoint lies in the carrier of its own chamber. -/
theorem val_mem_carrier_chamber (x : WallComplement W) : x.val ∈ (chamber x).carrier :=
  ConnectedComponents.mem_carrier_iff.mpr ⟨x.notMem, rfl⟩

/-- Every chamber is the chamber of an allowed endpoint. -/
theorem chamber_surjective : Function.Surjective (chamber (W := W)) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨⟨x.val, x.property⟩, rfl⟩

/-- A point lies in the carriers of at most one chamber. -/
theorem eq_of_mem_carrier {c c' : Chamber W} {z : V} (hz : z ∈ c.carrier)
    (hz' : z ∈ c'.carrier) : c = c' := by
  obtain ⟨_, rfl⟩ := ConnectedComponents.mem_carrier_iff.mp hz
  obtain ⟨_, rfl⟩ := ConnectedComponents.mem_carrier_iff.mp hz'
  rfl

/-- A preconnected set avoiding all walls lies in the carrier of the chamber of any
of its points. -/
theorem subset_carrier_of_isPreconnected {A : Set V} (hA : IsPreconnected A)
    (hAW : ∀ a ∈ A, ∀ i, a ∉ W i) {z : V} (hz : z ∈ A) {c : Chamber W}
    (hzc : z ∈ c.carrier) : A ⊆ c.carrier := by
  obtain ⟨hzW, rfl⟩ := ConnectedComponents.mem_carrier_iff.mp hzc
  rw [ConnectedComponents.carrier_mk]
  exact hA.subset_connectedComponentIn hz fun a ha => hAW a ha

/-- A preconnected set avoiding all walls lies in one chamber: an allowed endpoint in
it has the chamber of any of its points. -/
theorem chamber_eq_of_isPreconnected {A : Set V} (hA : IsPreconnected A)
    (hAW : ∀ a ∈ A, ∀ i, a ∉ W i) {x : WallComplement W} (hx : x.val ∈ A) {z : V}
    (hz : z ∈ A) {c : Chamber W} (hzc : z ∈ c.carrier) : chamber x = c :=
  eq_of_mem_carrier (val_mem_carrier_chamber x)
    (subset_carrier_of_isPreconnected hA hAW hz hzc hx)

variable [NormedSpace ℝ V]

/-- A segment meeting no wall joins two endpoints of the same chamber. -/
theorem chamber_eq_of_crossings_eq_empty {x y : WallComplement W}
    (he : crossings x y = ∅) : chamber x = chamber y := by
  have hA : ∀ a ∈ AffineMap.lineMap x.val y.val '' Icc (0 : ℝ) 1, ∀ i, a ∉ W i := by
    rintro _ ⟨t, ht, rfl⟩ i hi
    have hm : (i, t) ∈ crossings x y := (mem_crossings x y i t).mpr ⟨ht, hi⟩
    simp [he] at hm
  exact chamber_eq_of_isPreconnected
    (isPreconnected_Icc.image _ AffineMap.lineMap_continuous.continuousOn) hA
    ⟨0, ⟨le_rfl, zero_le_one⟩, AffineMap.lineMap_apply_zero _ _⟩
    ⟨1, ⟨zero_le_one, le_rfl⟩, AffineMap.lineMap_apply_one _ _⟩ (val_mem_carrier_chamber y)

end Mei.Convex.WallComplement
