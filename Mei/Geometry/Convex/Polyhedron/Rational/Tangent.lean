/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Analysis.Convex.TangentCone

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

/-- Every inequality is its value at `x` plus its linear part applied to the displacement. -/
theorem inequality_apply_eq (Q : RationalAffinePolyhedron h) (j : Fin Q.numConstraints)
    (x y : V) :
    Q.inequality j y = Q.inequality j x + (Q.inequality j).contLinear (y - x) := by
  have := (Q.inequality j).map_vadd x (y - x)
  simp only [vadd_eq_add, sub_add_cancel] at this
  rw [this, add_comm]

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
  have hloose : ∀ᶠ y in 𝓝 x, ∀ j, Q.inequality j x < 0 → Q.inequality j y < 0 :=
    eventually_all.mpr fun j => by
      by_cases hj : Q.inequality j x < 0
      · exact ((Q.inequality j).continuous.tendsto x).eventually (gt_mem_nhds hj) |>.mono
          fun y hy _ => hy
      · exact Eventually.of_forall fun y hlt => absurd hlt hj
  filter_upwards [hloose] with y hy
  rw [mem_carrier, mem_carrier_tangentAt]
  have hx : ∀ j, Q.inequality j x ≤ 0 := mem_carrier.mp hx
  constructor
  · intro hyQ j hj
    have := Q.inequality_apply_eq j x y
    rw [hj, zero_add] at this
    rw [← this]
    exact hyQ j
  · intro hv j
    rcases (hx j).lt_or_eq with hlt | heq
    · exact (hy j hlt).le
    · have := Q.inequality_apply_eq j x y
      rw [heq, zero_add] at this
      rw [this]
      exact hv j heq

/-- The tangent cone of a presented polyhedron at one of its points is the cone cut out by the
tight inequalities. -/
theorem posTangentConeAt_carrier (Q : RationalAffinePolyhedron h) {x : V}
    (hx : x ∈ Q.carrier) :
    posTangentConeAt Q.carrier x = (Q.tangentAt x).carrier := by
  ext v
  constructor
  · intro hv
    obtain ⟨α, l, hl, c, d, hd0, hdQ, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
    rw [mem_carrier_tangentAt]
    intro j hj
    have hcont : Continuous fun w => (Q.inequality j).contLinear w :=
      (Q.inequality j).contLinear.continuous
    refine le_of_tendsto (hcont.continuousAt.tendsto.comp hcd) ?_
    filter_upwards [hdQ] with n hn
    have hineq := Q.inequality_apply_eq j x (x + d n)
    rw [hj, zero_add, add_sub_cancel_left] at hineq
    have hle : (Q.inequality j).contLinear (d n) ≤ 0 := by
      rw [← hineq]
      exact mem_carrier.mp hn j
    simp only [Function.comp, NNReal.smul_def, map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (c n).2 hle
  · intro hv
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hseq : ∀ᶠ n : ℕ in atTop, x + ((n : ℝ)⁻¹ • v) ∈ Q.carrier := by
      have hlim : Tendsto (fun n : ℕ => x + ((n : ℝ)⁻¹ • v)) atTop (𝓝 (x + (0 : ℝ) • v)) :=
        tendsto_const_nhds.add (hinv.smul_const v)
      rw [zero_smul, add_zero] at hlim
      filter_upwards [hlim.eventually (Q.eventually_mem_carrier_iff hx)] with n hn
      rw [hn, add_sub_cancel_left]
      exact Q.smul_mem_carrier_tangentAt x hv (inv_nonneg.mpr n.cast_nonneg)
    refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => (n : NNReal))
      (fun n => (n : ℝ)⁻¹ • v) ?_ hseq ?_
    · simpa using hinv.smul_const v
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      simp [NNReal.smul_def, smul_smul, hn0]

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

/-- Near a point of a rational-normal polyhedron, the polyhedron is the translate of its
tangent cone at that point. -/
theorem eventually_mem_iff_sub_mem_posTangentConeAt (hP : IsRationalNormalPolyhedron h P)
    (hx : x ∈ P) : ∀ᶠ y in 𝓝 x, y ∈ P ↔ y - x ∈ _root_.posTangentConeAt P x := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  rw [Q.posTangentConeAt_carrier hx]
  exact Q.eventually_mem_carrier_iff hx

/-- The tangent cone of a rational-normal polyhedron is invariant under nonnegative scaling. -/
theorem smul_mem_posTangentConeAt (hP : IsRationalNormalPolyhedron h P) (hx : x ∈ P)
    {v : V} (hv : v ∈ _root_.posTangentConeAt P x) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ _root_.posTangentConeAt P x := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  rw [Q.posTangentConeAt_carrier hx] at hv ⊢
  exact Q.smul_mem_carrier_tangentAt x hv ht

/-- The tangent cone of a rational-normal polyhedron is closed under addition. -/
theorem add_mem_posTangentConeAt (hP : IsRationalNormalPolyhedron h P) (hx : x ∈ P)
    {u v : V} (hu : u ∈ _root_.posTangentConeAt P x) (hv : v ∈ _root_.posTangentConeAt P x) :
    u + v ∈ _root_.posTangentConeAt P x := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  rw [Q.posTangentConeAt_carrier hx] at hu hv ⊢
  exact Q.add_mem_carrier_tangentAt x hu hv

end IsRationalNormalPolyhedron

end Mei
