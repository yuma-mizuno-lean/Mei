/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.Tangent

/-!
# Tangent cones of rational-normal polyhedra

At a point `x` of a rational-normal polyhedron `P`, the one-sided tangent cone
`posTangentConeAt P x` is the rational-normal polyhedral cone cut out by the linear
parts of the inequalities of any presentation that are tight at `x`. The tight
inequalities are the only ones that matter near `x`, so `P` and the translate
`x + posTangentConeAt P x` agree on a neighbourhood of `x`. Offsets may be arbitrary
real numbers, inequalities may be redundant, and `P` may be unbounded or have lineality.

The presentation of the cone is `RationalAffinePolyhedron.tangentAt`; the cone itself
is Mathlib's `posTangentConeAt`.
-/

public section

open Filter Topology Set

namespace Mei

namespace RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The presentation by the linear parts of the inequalities that are tight at `x`. -/
noncomputable def tangentAt (Q : RationalAffinePolyhedron h) (x : V) :
    RationalAffinePolyhedron h :=
  ofFinite (ι := {j // Q.inequality j x = 0})
    (fun j => (Q.inequality j.1).contLinear.toContinuousAffineMap) fun j => by
      have hlin : ((Q.inequality j.1).contLinear.toContinuousAffineMap :
          V →ᴬ[ℝ] ℝ).linear = (Q.inequality j.1).linear := by
        simp only [← ContinuousAffineMap.coe_contLinear_eq_linear,
          ContinuousLinearMap.toContinuousAffineMap_contLinear]
      rw [hlin]
      exact Q.rational_linear j.1

/-- A displacement lies in the tangent presentation when it is nonpositive for the linear
part of every inequality tight at `x`. -/
@[simp high] -- Apply before `mem_carrier` exposes the presentation of the tangent cone.
theorem mem_carrier_tangentAt (Q : RationalAffinePolyhedron h) (x v : V) :
    v ∈ (Q.tangentAt x).carrier ↔
      ∀ j, Q.inequality j x = 0 → (Q.inequality j).contLinear v ≤ 0 := by
  rw [tangentAt, mem_carrier_ofFinite]
  simp

/-- The tangent presentation is a cone: it is invariant under nonnegative scaling. -/
theorem smul_mem_carrier_tangentAt (Q : RationalAffinePolyhedron h) (x : V) {v : V}
    (hv : v ∈ (Q.tangentAt x).carrier) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ (Q.tangentAt x).carrier := by
  rw [mem_carrier_tangentAt] at hv ⊢
  intro j hj
  rw [map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hv j hj)

/-- The tangent presentation is closed under addition. -/
theorem add_mem_carrier_tangentAt (Q : RationalAffinePolyhedron h) (x : V) {u v : V}
    (hu : u ∈ (Q.tangentAt x).carrier) (hv : v ∈ (Q.tangentAt x).carrier) :
    u + v ∈ (Q.tangentAt x).carrier := by
  rw [mem_carrier_tangentAt] at hu hv ⊢
  intro j hj
  rw [map_add]
  exact add_nonpos (hu j hj) (hv j hj)

/-- Near a point of the polyhedron, membership is membership of the displacement in the
tangent presentation: only the tight inequalities can fail. -/
theorem eventually_mem_carrier_iff (Q : RationalAffinePolyhedron h) {x : V}
    (hx : x ∈ Q.carrier) :
    ∀ᶠ y in 𝓝 x, y ∈ Q.carrier ↔ y - x ∈ (Q.tangentAt x).carrier := by
  filter_upwards [eventually_forall_affine_le_zero_iff Q.inequality (mem_carrier.mp hx)] with y hy
  rw [mem_carrier_tangentAt, mem_carrier]
  exact hy

/-- The tangent cone of a presented polyhedron at one of its points is the cone cut out by the
tight inequalities. -/
theorem posTangentConeAt_carrier (Q : RationalAffinePolyhedron h) {x : V}
    (hx : x ∈ Q.carrier) :
    posTangentConeAt Q.carrier x = (Q.tangentAt x).carrier := by
  have hcarrier : Q.carrier = {y | ∀ j, Q.inequality j y ≤ 0} :=
    Set.ext fun _ => mem_carrier
  rw [hcarrier, posTangentConeAt_setOf_forall_le_zero_eq Q.inequality (mem_carrier.mp hx)]
  ext v
  exact (Q.mem_carrier_tangentAt x v).symm

end RationalAffinePolyhedron

namespace IsRationalNormalPolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} {x : V}

/-- The tangent cone of a rational-normal polyhedron at one of its points is again a
rational-normal polyhedron. -/
theorem posTangentConeAt (hP : IsRationalNormalPolyhedron h P) (hx : x ∈ P) :
    IsRationalNormalPolyhedron h (_root_.posTangentConeAt P x) := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  exact isRationalNormalPolyhedron_iff.mpr ⟨Q.tangentAt x, (Q.posTangentConeAt_carrier hx).symm⟩

end IsRationalNormalPolyhedron

end Mei
