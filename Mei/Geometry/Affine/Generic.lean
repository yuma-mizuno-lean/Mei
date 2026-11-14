/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Exceptional arrangements

A locally finite-dimensional avoidance argument gives generic points on a face.
Exceptional arrangements package the forbidden affine subspaces and transport
them along affine equivalences.
-/

public section

open Set

namespace Mei

section Hyperplane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A set covered by countably many affine subspaces of ambient codimension at least two
has dense complement in a hyperplane: every point of the hyperplane is a limit of points
of the hyperplane outside the set. -/
theorem face_subset_closure_sdiff_of_finrank {ι : Sort*} [Countable ι]
    {ν : V →L[ℝ] ℝ} {b : ℝ} {Z : Set V} (hν : ν ≠ 0)
    (E : ι → AffineSubspace ℝ V) (hZE : Z ⊆ ⋃ i, (E i : Set V))
    (hE : ∀ i, Module.finrank ℝ (E i).direction + 1 < Module.finrank ℝ V) :
    {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z) := by
  intro x hx
  have hx' : ν x = b := hx
  -- The face is the affine subspace through `x` with direction `ker ν`.
  let A : AffineSubspace ℝ V := .mk' x (LinearMap.ker ν.toLinearMap)
  have hA : ∀ y ∈ A, ν y = b := fun y hy => by
    have := AffineSubspace.mem_mk'.mp hy
    simpa [sub_eq_zero, hx'] using this
  have hdir : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V := by
    rw [AffineSubspace.direction_mk']
    exact Module.Dual.finrank_ker_add_one_of_ne_zero (f := ν.toLinearMap)
      (fun h => hν (ContinuousLinearMap.coe_injective h))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hzE⟩ := A.exists_mem_open_avoid_of_finrank_lt E
    (fun i => by have := hE i; omega) (U := Subtype.val ⁻¹' Metric.ball x ε)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
    ⟨⟨x, AffineSubspace.self_mem_mk' x _⟩, Metric.mem_ball_self hε⟩
  exact ⟨z, ⟨hA z z.2, fun hzZ => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hZE hzZ)
    exact hzE i hi⟩, by simpa [dist_comm] using hz⟩

end Hyperplane

end Mei
