/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed

/-!
# Simultaneous wall events

An event records the nonempty set of all indexed walls through its point and a
crossing sign. Its support requires exactly that incidence set, retaining every
index of coincident walls. Choosing one incident wall supplies a normal and an
offset. Supports with the same incidence set and opposite signs coincide; the
normal velocity distinguishes their signed encounters.

These events give a finite encounter alphabet for rays through a finite wall
family. Their supports are rational semilinear whenever the original supports
are. This uses finite Boolean closure of `IsRationalSemilinear`; grouping
simultaneous crossings follows `WallComplement.signedCrossingEvent`.
-/

public noncomputable section

open Set

namespace Mei.Convex

/-- A nonempty simultaneous incidence set, together with its crossing sign.
The indices of coincident walls are retained separately in the incidence set. -/
abbrev WallEvent (ι : Type*) := {s : Finset ι // s.Nonempty} × SignType

namespace WallEvent

variable {ι V : Type*}

/-- The points lying on exactly the walls recorded by an event. -/
def support (e : WallEvent ι) (W : ι → Set V) : Set V :=
  {x | ∀ j, x ∈ W j ↔ j ∈ e.1.val}

/-- Event support is characterized by the complete indexed incidence set. -/
@[simp]
theorem mem_support (e : WallEvent ι) (W : ι → Set V) (x : V) :
    x ∈ e.support W ↔ ∀ j, x ∈ W j ↔ j ∈ e.1.val := Iff.rfl

/-- Every event point belongs to each of its recorded walls. -/
theorem support_subset (e : WallEvent ι) (W : ι → Set V) {j : ι}
    (hj : j ∈ e.1.val) : e.support W ⊆ W j :=
  fun _ hx => (mem_support e W _).mp hx j |>.mpr hj

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Choose the normal of one recorded wall as the event's normal. -/
def normal (e : WallEvent ι) (f : ι → V →L[ℝ] ℝ) : V →L[ℝ] ℝ :=
  f e.1.property.choose

/-- Use the offset of the same wall chosen for the event normal. -/
def offset (e : WallEvent ι) (c : ι → ℝ) : ℝ := c e.1.property.choose

/-- The event normal is the normal at its chosen recorded wall index. -/
@[simp]
theorem normal_def (e : WallEvent ι) (f : ι → V →L[ℝ] ℝ) :
    e.normal f = f e.1.property.choose := (rfl)

/-- The event offset uses the same recorded wall index as its normal. -/
@[simp]
theorem offset_def (e : WallEvent ι) (c : ι → ℝ) :
    e.offset c = c e.1.property.choose := (rfl)

/-- Exact incidence and the prescribed normal-velocity signs distinguish
all signed event labels, including opposite signs on the same support. -/
theorem eq_of_mem_support_of_normal_sign_eq (e e' : WallEvent ι) (W : ι → Set V)
    (f : ι → V →L[ℝ] ℝ) (v : V) {x : V}
    (hx : x ∈ e.support W) (hx' : x ∈ e'.support W)
    (hs : SignType.sign (e.normal f v) = e.2)
    (hs' : SignType.sign (e'.normal f v) = e'.2) : e = e' := by
  have he : e.1 = e'.1 := Subtype.ext (Finset.ext fun j => (hx j).symm.trans (hx' j))
  apply Prod.ext he
  rw [← hs, ← hs', normal_def, normal_def, he]

/-- Event points lie on the hyperplane of their chosen incident wall. -/
theorem normal_apply_of_mem_support (e : WallEvent ι) (W : ι → Set V)
    (f : ι → V →L[ℝ] ℝ) (c : ι → ℝ)
    (hW : ∀ j x, x ∈ W j → f j x = c j) {x : V} (hx : x ∈ e.support W) :
    e.normal f x = e.offset c :=
  hW _ _ (e.support_subset W e.1.property.choose_spec hx)

/-- Transversality to every incident wall implies transversality to the event. -/
theorem normal_ne_zero_of_mem_support (e : WallEvent ι) (W : ι → Set V)
    (f : ι → V →L[ℝ] ℝ) {x v : V} (hx : x ∈ e.support W)
    (hv : ∀ j, x ∈ W j → f j v ≠ 0) : e.normal f v ≠ 0 :=
  hv _ (e.support_subset W e.1.property.choose_spec hx)

variable [Finite ι]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Passing to simultaneous events preserves the union of all wall supports. -/
@[simp]
theorem iUnion_support (W : ι → Set V) :
    (⋃ e : WallEvent ι, e.support W) = ⋃ j, W j := by
  classical
  let := Fintype.ofFinite ι
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨_, e.support_subset W e.1.property.choose_spec he⟩
  · rintro ⟨j, hj⟩
    let s := Finset.univ.filter fun i => x ∈ W i
    have hs : s.Nonempty := ⟨j, by simpa [s] using hj⟩
    exact ⟨(⟨s, hs⟩, 1), by simp [support, s]⟩

/-- Exact simultaneous incidence remains rational semilinear, although the
event supports need not be closed. -/
theorem isRationalSemilinear_support {N : Type*} [AddCommGroup N] {i : N →+ V}
    {h : TauCeti.Toric.IsIntegralLattice i} (e : WallEvent ι) (W : ι → Set V)
    (hW : ∀ j, IsRationalSemilinear h (W j)) : IsRationalSemilinear h (e.support W) := by
  classical
  have he : e.support W = ⋂ j, if j ∈ e.1.val then W j else (W j)ᶜ := by
    ext x
    simp only [mem_support, mem_iInter]
    exact forall_congr' fun j => by split_ifs <;> simp_all
  rw [he]
  exact IsRationalSemilinear.iInter fun j => by
    split_ifs
    · exact hW j
    · exact (hW j).compl

end WallEvent
end Mei.Convex
