/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Geometry.Affine.Generic

/-!
# Exceptional arrangements from affine subspaces

The exceptions of an exceptional arrangement are usually affine spans rather than
zero sets of chosen affine functionals: the endpoint discriminant of the closed-chart
construction is assembled from the spans of the shadows of the singular-support cells.
This file provides that constructor. A finite family of affine subspaces is an
exceptional arrangement once the ambient space is dropped, the empty family is
allowed, and a generic point is a point outside every member.

The constructor is the same lattice operation as `Mei.ExceptionalArrangement.union`:
the exceptions are the union of the given finsets. Genericity of a point is
therefore the conjunction over the family, and the generic locus is open in finite
dimension. No affine functional representing a member is required, and members may
have any codimension, including zero before the ambient space is removed.
-/

public section

noncomputable section

open Set

namespace Mei.ExceptionalArrangement

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The arrangement of a finite family of affine subspaces. The ambient space
contributes no exception, so a family of spans is admissible without a constraint
on its members. -/
def ofSubspaces (S : Finset (AffineSubspace ℝ V)) : ExceptionalArrangement V := by
  classical
  exact ⟨S.erase ⊤, fun _ h => Finset.ne_of_mem_erase h⟩

open Classical in
/-- The exceptions of the arrangement of a finite family are its proper members. -/
@[simp]
theorem exceptions_ofSubspaces (S : Finset (AffineSubspace ℝ V)) :
    (ofSubspaces S).exceptions = S.erase ⊤ := (rfl)

/-- A point is generic for the arrangement of a finite family exactly when it lies
in none of the proper members. -/
@[simp]
theorem isGeneric_ofSubspaces_iff (S : Finset (AffineSubspace ℝ V)) (x : V) :
    (ofSubspaces S).IsGeneric x ↔ ∀ T ∈ S, T ≠ ⊤ → x ∉ T := by
  classical
  rw [isGeneric_iff, exceptions_ofSubspaces]
  simp only [Finset.mem_erase, ne_eq, and_imp]
  exact ⟨fun h T hT htop => h T htop hT, fun h T htop hT => h T hT htop⟩

/-- The arrangement of a finite index family of subspaces. -/
def ofFinset {ι : Type*} [Fintype ι] (T : ι → AffineSubspace ℝ V) :
    ExceptionalArrangement V := by
  classical
  exact ofSubspaces (Finset.univ.image T)

/-- A point is generic for the arrangement of a finite index family exactly when it
lies in none of the proper members. -/
@[simp]
theorem isGeneric_ofFinset_iff {ι : Type*} [Fintype ι] (T : ι → AffineSubspace ℝ V)
    (x : V) : (ofFinset T).IsGeneric x ↔ ∀ i, T i ≠ ⊤ → x ∉ T i := by
  classical
  rw [ofFinset, isGeneric_ofSubspaces_iff]
  constructor
  · intro h i hi
    exact h (T i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hi
  · rintro h U hU hUtop
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hU
    exact h i hUtop

end Mei.ExceptionalArrangement
