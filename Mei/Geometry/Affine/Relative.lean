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

Countably many affine subspaces of smaller dimension cannot cover a nonempty
relatively open subset of an affine subspace. In particular, they can be avoided
in any prescribed open set meeting the intrinsic interior of a set.
This permits choosing points on walls while avoiding singular strata of other
polyhedral complexes, even for a countable sequence of complexes.

The construction applies `AffineSubspace.exists_mem_open_genericLocus` after
translation to the direction space, using Mathlib's affine isometry
`AffineIsometryEquiv.constVSub` and intrinsic interior.
-/

public noncomputable section

open Set

namespace AffineSubspace

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι]

/-- A nonempty relatively open set in an affine subspace contains a point
outside any countable family of affine subspaces of smaller dimension. -/
theorem exists_mem_open_avoid_of_finrank_lt (A : AffineSubspace ℝ V)
    (E : ι → AffineSubspace ℝ V)
    (hE : ∀ j, Module.finrank ℝ (E j).direction < Module.finrank ℝ A.direction)
    {U : Set A} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ j, (x : V) ∉ E j := by
  obtain ⟨p, hp⟩ := hne
  let : Nonempty A := ⟨p⟩
  let e := (AffineIsometryEquiv.constVSub ℝ p).symm
  let f := A.subtype.comp e.toAffineEquiv.toAffineMap
  have hproper (j : ι) : (E j).comap f ≠ ⊤ := by
    intro hj
    have hle : A ≤ E j := by
      intro y hy
      have hv : e.symm ⟨y, hy⟩ ∈ (E j).comap f := by rw [hj]; trivial
      simpa only [mem_comap, f, AffineMap.comp_apply, coe_subtype,
        AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
        e.apply_symm_apply] using hv
    exact (not_le_of_gt (hE j)) (Submodule.finrank_mono (direction_le hle))
  obtain ⟨v, hv, havoid⟩ := exists_mem_open_genericLocus
    (fun j => (E j).comap f) hproper
    (hU.preimage e.continuous) ⟨e.symm p, by simpa using hp⟩
  exact ⟨e v, hv, havoid⟩

end AffineSubspace

namespace Set

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι]

/-- In any open set meeting a set's intrinsic interior, there is an
intrinsic interior point avoiding countably many smaller-dimensional affine
subspaces. The open set is taken in the ambient space. -/
theorem exists_mem_intrinsicInterior_avoid_of_finrank_lt (P : Set V)
    (E : ι → AffineSubspace ℝ V)
    (hE : ∀ j, Module.finrank ℝ (E j).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction)
    {U : Set V} (hU : IsOpen U) (hne : (U ∩ intrinsicInterior ℝ P).Nonempty) :
    ∃ x ∈ U ∩ intrinsicInterior ℝ P, ∀ j, x ∉ E j := by
  let A := affineSpan ℝ P
  let W : Set A := (Subtype.val ⁻¹' U) ∩ interior (Subtype.val ⁻¹' P)
  have hW : IsOpen W := (hU.preimage continuous_subtype_val).inter isOpen_interior
  obtain ⟨x, hxU, hxP⟩ := hne
  obtain ⟨xA, hxA, rfl⟩ := mem_intrinsicInterior.mp hxP
  obtain ⟨y, ⟨hyU, hyP⟩, hy⟩ :=
    A.exists_mem_open_avoid_of_finrank_lt E hE hW ⟨xA, hxU, hxA⟩
  exact ⟨y, ⟨hyU, mem_intrinsicInterior.mpr ⟨y, hyP, rfl⟩⟩, hy⟩

end Set
