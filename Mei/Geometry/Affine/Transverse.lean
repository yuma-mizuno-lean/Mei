/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Transverse lines and affine subspaces

A line whose direction is outside an affine subspace's direction meets that
subspace at most once, counted by its affine parameter. More generally, the
affine span of finitely many points meets an affine subspace at most once when
the edge vectors from the first point are linearly independent modulo the
subspace's direction.
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

/-- If the edge vectors `p j.succ -ᵥ p 0` of a finite family of points remain linearly
independent modulo the direction of `S`, then the affine span of the points meets `S` in at most
one point. -/
theorem subsingleton_affineSpan_range_inter (S : AffineSubspace k P) {n : ℕ}
    {p : Fin (n + 1) → P}
    (hp : LinearIndependent k (S.direction.mkQ ∘ fun j : Fin n => p j.succ -ᵥ p 0)) :
    ((affineSpan k (Set.range p) : Set P) ∩ S).Subsingleton := by
  intro x hx y hy
  have hxy : x -ᵥ y ∈ Submodule.span k (Set.range fun j : Fin n => p j.succ -ᵥ p 0) := by
    have hmem := (affineSpan k (Set.range p)).vsub_mem_direction hx.1 hy.1
    rw [direction_affineSpan, vectorSpan_range_eq_span_range_vsub_right_ne k p 0] at hmem
    convert hmem using 2
    ext w
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.succ, Fin.succ_ne_zero j⟩, rfl⟩
    · rintro ⟨⟨l, hl⟩, rfl⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hl
      exact ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun k |>.mp hxy
  have hc0 := Fintype.linearIndependent_iff.mp hp c <| by
    have hS : S.direction.mkQ (x -ᵥ y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (S.vsub_mem_direction hx.2 hy.2)
    rw [← hc, map_sum] at hS
    simpa only [Function.comp_apply, map_smul] using hS
  rw [← vsub_eq_zero_iff_eq, ← hc]
  simp [hc0]

end AffineSubspace
