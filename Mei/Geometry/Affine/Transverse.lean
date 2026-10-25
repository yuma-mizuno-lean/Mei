/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Transverse lines and affine subspaces

A line whose direction is outside an affine subspace's direction meets that
subspace at most once, counted by its affine parameter.
-/

public section

namespace AffineSubspace

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

/-- The parameters at which a transverse line meets an affine subspace form
a subsingleton. No codimension or nonemptiness assumption is needed. -/
theorem subsingleton_preimage_lineMap (S : AffineSubspace k P) {x y : P}
    (h : y -ᵥ x ∉ S.direction) :
    ((AffineMap.lineMap x y : k →ᵃ[k] P) ⁻¹' (S : Set P)).Subsingleton := by
  classical
  intro s hs t ht
  by_contra hst
  have hd := S.vsub_mem_direction hs ht
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply,
    vadd_vsub_vadd_cancel_right, ← sub_smul] at hd
  exact h ((S.direction.smul_mem_iff (sub_ne_zero.mpr hst)).mp hd)

end AffineSubspace
