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
import Mei.Geometry.Convex.Polyhedron.Escape

/-!
# Open ray encounters and eventual source admission

The base points whose open positive ray along a lattice vector meets a closed
rational-normal polyhedron form a locally closed rational-normal polyhedron.
The nonnegative sweep gives the weak conditions; rows increasing along the ray
must additionally be strictly negative at its base. This excludes intersections
occurring only at parameter zero, while retaining positive isolated intersections
and rays tangent to the support.

Eventual membership along any real direction has a closed rational-normal domain:
it is a nonnegative sweep for recession directions and empty otherwise.
In recession directions, only the inequalities constant along the ray remain.
These two results supply wall avoidance and source admission for unbounded incoming
segments.

The construction reuses `IsRationalNormalPolyhedron.negRay` and the active-inequality
perturbation theorem `AffineMap.exists_pos_smul_add_forall_le`, together with
`Convex.eventually_forall_notMem_of_notMem_recessionCone` for nonrecession directions.
-/

public section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- The base points of open positive rays along a lattice vector meeting a closed
rational-normal polyhedron form a locally closed rational-normal polyhedron.
The vector may be zero or tangent to the polyhedron, and the intersection may be
a single point. -/
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

/-- Eventual admission along any real direction has a closed rational-normal domain,
including for empty sources and zero directions. Outside the recession cone,
the domain is empty. -/
theorem IsRationalNormalPolyhedron.eventually_add_smul_mem
    (hP : IsRationalNormalPolyhedron h P) (w : V) :
    IsRationalNormalPolyhedron h
      {x : V | ∀ᶠ t : ℝ in Filter.atTop, x + t • w ∈ P} := by
  classical
  by_cases hne : P.Nonempty
  · obtain ⟨A, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
    by_cases hw : w ∈ Set.recessionCone A.carrier
    · have hlin : ∀ j, (A.inequality j).linear w ≤ 0 := by
        have hcarrier : A.carrier = {x | ∀ j, A.inequality j x ≤ 0} :=
          Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
        rw [hcarrier] at hne hw
        exact (Set.mem_recessionCone_setOf_forall_iff
          (g := fun j => (A.inequality j).toAffineMap) hne).mp hw
      let J := {j : Fin A.numConstraints // (A.inequality j).linear w = 0}
      have he : {x : V | ∀ᶠ t : ℝ in Filter.atTop, x + t • w ∈ A.carrier} =
          {x | ∀ j : J, A.inequality j.val x ≤ 0} := by
        ext x
        simp only [Set.mem_ofPred_eq, RationalAffinePolyhedron.mem_carrier,
          Filter.eventually_all]
        constructor
        · intro hx j
          simpa only [ContinuousAffineMap.apply_add_smul, j.property, zero_mul,
            add_zero, Filter.eventually_const] using hx j.val
        · intro hx j
          rcases (hlin j).eq_or_lt with hj | hj
          · exact Filter.Eventually.of_forall fun t => by
              simpa only [ContinuousAffineMap.apply_add_smul, hj, zero_mul, add_zero]
                using hx ⟨j, hj⟩
          · filter_upwards [Filter.eventually_ge_atTop
              (-A.inequality j x / (A.inequality j).linear w)] with t ht
            rw [ContinuousAffineMap.apply_add_smul]
            have := (div_le_iff_of_neg hj).mp ht
            linarith
      rw [he]
      exact isRationalNormalPolyhedron_setOf_forall (fun j : J => A.inequality j.val)
        (fun j => A.rational_linear j.val)
    · have he : {x : V | ∀ᶠ t : ℝ in Filter.atTop, x + t • w ∈ A.carrier} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hescape := Convex.eventually_forall_notMem_of_notMem_recessionCone
          A.isConvexPolyhedron hw (K := {x}) isCompact_singleton
        obtain ⟨t, ht, htP⟩ := (hescape.and hx).exists
        exact ht x (Set.mem_singleton x) htP
      rw [he]
      exact IsRationalNormalPolyhedron.empty h
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Set.mem_empty_iff_false, Filter.eventually_const, Set.ofPred_false]
      using IsRationalNormalPolyhedron.empty h (V := V)

end Mei
