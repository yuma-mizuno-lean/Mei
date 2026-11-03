/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mei.Topology.Connected.Adjacency
public import Mei.Topology.Connected.Homeomorph

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

A homeomorphism carrying one wall family onto another, with the indices matched by a
bijection, identifies the chambers (`chamberEquiv`), compatibly with the chambers of
allowed endpoints and with the ambient carriers.
-/

public section

open Set

namespace Mei.Convex.WallComplement

section Topological

variable {V ι : Type*} [TopologicalSpace V] {W : ι → Set V}

/-- The chambers of a wall family: the connected components of the complement of
all walls, with the subspace topology. -/
abbrev Chamber (W : ι → Set V) := ConnectedComponents {x : V | ∀ i, x ∉ W i}

/-- The chamber containing an allowed endpoint. -/
def chamber (x : WallComplement W) : Chamber W :=
  ConnectedComponents.mk ⟨x.val, x.notMem⟩

/-- An allowed endpoint lies in the carrier of its own chamber. -/
@[simp]
theorem val_mem_carrier_chamber (x : WallComplement W) : x.val ∈ (chamber x).carrier :=
  ConnectedComponents.mem_carrier_iff.mpr ⟨x.notMem, rfl⟩

/-- Every chamber is the chamber of an allowed endpoint. -/
theorem chamber_surjective : Function.Surjective (chamber (W := W)) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨⟨x.val, x.property⟩, rfl⟩

/-- A preconnected set avoiding all walls lies in one chamber: an allowed endpoint in
it has the chamber of any of its points. -/
theorem chamber_eq_of_isPreconnected {A : Set V} (hA : IsPreconnected A)
    (hAW : ∀ a ∈ A, ∀ i, a ∉ W i) {x : WallComplement W} (hx : x.val ∈ A) {z : V}
    (hz : z ∈ A) {c : Chamber W} (hzc : z ∈ c.carrier) : chamber x = c :=
  ConnectedComponents.eq_of_mem_carrier (val_mem_carrier_chamber x)
    (ConnectedComponents.subset_carrier_of_isPreconnected hA (fun a ha => hAW a ha) hz hzc hx)

section Transport

variable {V' ι' : Type*} [TopologicalSpace V'] {W' : ι' → Set V'}
  (e : V ≃ₜ V') (r : ι ≃ ι') (hW : ∀ j, W' (r j) = e '' W j)

/-- A homeomorphism carrying a wall family onto another, with the wall indices matched by
a bijection, identifies the chambers of the two families. -/
def chamberEquiv : Chamber W ≃ Chamber W' :=
  (e.sets (s := {x : V | ∀ i, x ∉ W i}) (t := {y : V' | ∀ j, y ∉ W' j})
    (Set.ext fun x => by
      refine ⟨fun hx j hj => ?_, fun hx i hi => hx (r i) ?_⟩
      · obtain ⟨i, rfl⟩ := r.surjective j
        rw [hW, e.injective.mem_set_image] at hj
        exact hx i hj
      · rw [hW]
        exact mem_image_of_mem e hi)).connectedComponentsEquiv

include hW in
/-- The identification of chambers sends the chamber of an allowed endpoint to the chamber
of any allowed endpoint at its image. -/
theorem chamberEquiv_chamber (x : WallComplement W) (x' : WallComplement W')
    (hx : x'.val = e x.val) : chamberEquiv e r hW (chamber x) = chamber x' := by
  obtain ⟨v, hv⟩ := x'
  dsimp only at hx
  subst hx
  simp only [chamberEquiv, chamber, Homeomorph.connectedComponentsEquiv_mk]
  exact congrArg ConnectedComponents.mk (Subtype.ext (rfl))

include hW in
/-- A point of the carrier of a chamber is carried into the carrier of the identified chamber. -/
theorem image_mem_carrier_chamberEquiv {c : Chamber W} {z : V} (hz : z ∈ c.carrier) :
    e z ∈ (chamberEquiv e r hW c).carrier := by
  obtain ⟨hz', rfl⟩ := ConnectedComponents.mem_carrier_iff.mp hz
  have hz'' : ∀ j, e z ∉ W' j := fun j hj => by
    obtain ⟨i, rfl⟩ := r.surjective j
    rw [hW, e.injective.mem_set_image] at hj
    exact hz' i hj
  exact ConnectedComponents.mem_carrier_iff.mpr
    ⟨hz'', (chamberEquiv_chamber e r hW ⟨z, hz'⟩ ⟨e z, hz''⟩ rfl).symm⟩

end Transport

end Topological

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}

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
