/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep
public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed
public import Mei.Geometry.Convex.Recession
import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Open ray encounters and eventual source admission

The base points whose open positive ray meets a closed rational-normal polyhedron
form a locally closed rational-normal polyhedron. The nonnegative sweep gives the
weak conditions; rows increasing along the ray must additionally be strictly
negative at its base. This excludes intersections occurring only at parameter zero,
while retaining positive isolated intersections and rays tangent to the support.

For a recession direction, eventual membership is a nonnegative sweep and therefore
has a closed rational-normal domain. These two results supply wall avoidance and
source admission for unbounded incoming segments.

The construction reuses `IsRationalNormalPolyhedron.negRay` and the active-inequality
perturbation theorem `AffineMap.exists_pos_smul_add_forall_le`.
-/

public section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- The base points of open positive rays meeting a closed rational-normal
polyhedron form a locally closed rational-normal polyhedron. The vector may be zero
or tangent to the polyhedron, and the intersection may be a single point. -/
theorem IsRationalNormalPolyhedron.isLocallyClosedPolyhedron_posRay
    (hP : IsRationalNormalPolyhedron h P) (w : N) :
    IsLocallyClosedPolyhedron h {x : V | ∃ t : ℝ, 0 < t ∧ x + t • i w ∈ P} := by
  obtain ⟨A, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  let J := {j : Fin A.numConstraints // 0 < (A.inequality j).linear (i w)}
  have he : {x : V | ∃ t : ℝ, 0 < t ∧ x + t • i w ∈ A.carrier} =
      {x : V | ∃ t : ℝ, 0 ≤ t ∧ x + t • i w ∈ A.carrier} ∩
        {x | ∀ j : J, A.inequality j.val x < 0} := by
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      refine ⟨⟨t, ht.le, hx⟩, fun j => ?_⟩
      have hj := (RationalAffinePolyhedron.mem_carrier.mp hx) j.val
      rw [ContinuousAffineMap.apply_add_smul] at hj
      have hpos := mul_pos ht j.property
      linarith
    · rintro ⟨⟨t, ht, hx⟩, hstrict⟩
      rcases ht.eq_or_lt with rfl | ht
      · simp only [zero_smul, add_zero] at hx
        have hactive (j : Fin A.numConstraints) (hj : A.inequality j x = 0) :
            (A.inequality j).linear (i w) ≤ 0 := by
          by_contra hle
          have hs := hstrict ⟨j, lt_of_not_ge hle⟩
          linarith
        obtain ⟨ε, hε, hmem⟩ := AffineMap.exists_pos_smul_add_forall_le
          (fun j => (A.inequality j).toAffineMap)
          (RationalAffinePolyhedron.mem_carrier.mp hx) hactive
        exact ⟨ε, hε, RationalAffinePolyhedron.mem_carrier.mpr
          (fun j => by
            simpa only [ContinuousAffineMap.coe_toAffineMap, add_comm] using hmem j)⟩
      · exact ⟨t, ht, hx⟩
  rw [he]
  have hweak := (isRationalNormalPolyhedron_iff.mpr ⟨A, rfl⟩).negRay w
  exact hweak.isLocallyClosedPolyhedron_inter (fun j : J => A.inequality j.val)
    (fun j => A.rational_linear j.val)

/-- Eventual admission along a lattice recession direction has a closed
rational-normal domain, including for empty sources and zero directions. -/
theorem IsRationalNormalPolyhedron.eventually_add_smul_mem
    (hP : IsRationalNormalPolyhedron h P) (w : N) (hw : i w ∈ Set.recessionCone P) :
    IsRationalNormalPolyhedron h
      {x : V | ∀ᶠ t : ℝ in Filter.atTop, x + t • i w ∈ P} := by
  simpa only [Set.eventually_add_smul_mem_atTop_iff hw] using hP.negRay w

end Mei
