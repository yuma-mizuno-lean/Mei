/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# Relative generic points

Countably many affine subspaces, none containing the affine span of a set,
can be avoided in any prescribed open set meeting its intrinsic interior.
In particular, this applies to affine obstacles of smaller dimension.
This permits choosing points on walls while avoiding singular strata of other
polyhedral complexes, even for a countable sequence of complexes.

The construction applies `AffineSubspace.exists_mem_open_avoid_of_not_le`
to Mathlib's description of intrinsic interior as relative interior in the
affine span.
-/

public noncomputable section

open Set

namespace Set

variable {V : Type*} {ι : Sort*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι]

/-- In any open set meeting a set's intrinsic interior, there is an
intrinsic interior point avoiding countably many affine subspaces, none
containing its affine span. The open set is taken in the ambient space. -/
theorem exists_mem_intrinsicInterior_avoid_of_not_le (P : Set V)
    (E : ι → AffineSubspace ℝ V)
    (hE : ∀ j, ¬ affineSpan ℝ P ≤ E j)
    {U : Set V} (hU : IsOpen U) (hne : (U ∩ intrinsicInterior ℝ P).Nonempty) :
    ∃ x ∈ U ∩ intrinsicInterior ℝ P, ∀ j, x ∉ E j := by
  let A := affineSpan ℝ P
  let W : Set A := (Subtype.val ⁻¹' U) ∩ interior (Subtype.val ⁻¹' P)
  have hW : IsOpen W := (hU.preimage continuous_subtype_val).inter isOpen_interior
  obtain ⟨x, hxU, hxP⟩ := hne
  obtain ⟨xA, hxA, rfl⟩ := mem_intrinsicInterior.mp hxP
  obtain ⟨y, ⟨hyU, hyP⟩, hy⟩ :=
    A.exists_mem_open_avoid_of_not_le E hE hW ⟨xA, hxU, hxA⟩
  exact ⟨y, ⟨hyU, mem_intrinsicInterior.mpr ⟨y, hyP, rfl⟩⟩, hy⟩

/-- In any open set meeting a set's intrinsic interior, there is an
intrinsic interior point avoiding countably many smaller-dimensional affine
subspaces. The open set is taken in the ambient space. -/
theorem exists_mem_intrinsicInterior_avoid_of_finrank_lt (P : Set V)
    (E : ι → AffineSubspace ℝ V)
    (hE : ∀ j, Module.finrank ℝ (E j).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction)
    {U : Set V} (hU : IsOpen U) (hne : (U ∩ intrinsicInterior ℝ P).Nonempty) :
    ∃ x ∈ U ∩ intrinsicInterior ℝ P, ∀ j, x ∉ E j :=
  P.exists_mem_intrinsicInterior_avoid_of_not_le E
    (fun j hle => (not_le_of_gt (hE j))
      (Submodule.finrank_mono (AffineSubspace.direction_le hle))) hU hne

end Set
