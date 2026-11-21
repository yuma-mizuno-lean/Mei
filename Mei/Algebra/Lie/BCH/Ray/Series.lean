/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series along a ray of a positively graded Lie algebra

Let `n` be a nonzero allowed degree of positive degree data and let `x : ℕ → L` be a family
with `x j` homogeneous of degree `(j+1) n`. A formal power series `f = ∑ f_j Tʲ` defines the
completed Lie element `∑_{j ≥ 0} f_{j+1} x j` (`PositiveDegrees.raySeries`); its order-`k`
projection is the class of the finite sum over `j < k`, since `δ((j+1)n) > j`. The constant
coefficient is ignored. If the elements `x j` commute pairwise, so do these completed elements,
and their completed exponentials `PositiveDegrees.rayExp` form a homomorphic image of the
additive group of power series. Every `rayExp` lies in the completed ray subgroup of a
supported ray containing `n`, and its logarithmic coefficient in degree `(j+1)n` is
`f_{j+1} x j`.

These are the labels `exp(∑ f_j z^{jn})` along a ray, for instance the quantum dilogarithm
labels of quantum scattering diagrams. The construction uses `ModuleFiltration.lift` for the
compatible finite sums and `PositiveDegrees.completedBCHExp` for the levelwise exponentials;
coefficients are read by `PositiveDegrees.logComponent_eq_decompose`.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open PowerSeries

variable {N R L : Type*} [AddCommGroup N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) {n : N} (x : ℕ → L)

local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- The finite sum `∑_{j < k} f_{j+1} x j`. -/
def rayPartialSum (k : ℕ) : R⟦X⟧ →ₗ[R] L :=
  ∑ j ∈ Finset.range k, (coeff (j + 1)).smulRight (x j)

/-- The partial ray sum is `∑_{j < k} f_{j+1} x j`. -/
@[simp]
theorem rayPartialSum_apply (k : ℕ) (f : R⟦X⟧) :
    rayPartialSum x k f = ∑ j ∈ Finset.range k, coeff (j + 1) f • x j := by
  simp [rayPartialSum]

variable [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hx : ∀ j, x j ∈ ℒ ((j + 1) • n))

include hn hn0 hx

/-- Terms beyond order `k` lie in the degree ideal above `k`. -/
theorem rayPartialSum_sub_mem {k l : ℕ} (h : k ≤ l) (f : R⟦X⟧) :
    rayPartialSum x l f - rayPartialSum x k f ∈ d.degreeIdeal ℒ k := by
  rw [rayPartialSum_apply, rayPartialSum_apply, ← Finset.sum_range_add_sum_Ico _ h,
    add_sub_cancel_left]
  refine Submodule.sum_mem (d.degreeIdeal ℒ k).toSubmodule fun j hj => ?_
  apply d.le_degreeIdeal ℒ (lt_of_le_of_lt _ (d.lt_degree_succ_nsmul hn hn0 j))
    ((ℒ _).smul_mem _ (hx j))
  exact_mod_cast (Finset.mem_Ico.mp hj).1

/-- The completed Lie element `∑_{j ≥ 0} f_{j+1} x j` of a power series `f`. -/
def raySeries : R⟦X⟧ →ₗ[R] d.completedLie ℒ :=
  (F).lift (fun k => (d.degreeIdeal ℒ k).toSubmodule.mkQ ∘ₗ rayPartialSum x k) (by
    intro k l h
    ext f
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply,
      Mei.ModuleFiltration.transition_mk]
    exact (Submodule.Quotient.eq _).mpr (rayPartialSum_sub_mem d ℒ x hn hn0 hx h f))

/-- At order `k`, the ray series is the class of its partial sum over `j < k`. -/
@[simp]
theorem completionProjection_raySeries (k : ℕ) (f : R⟦X⟧) :
    LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k
        (d.raySeries ℒ x hn hn0 hx f) =
      (d.degreeIdeal ℒ k).mkQ (rayPartialSum x k f) := by
  rw [LieIdeal.completionProjection_apply, raySeries, Mei.ModuleFiltration.projection_lift]
  -- The submodule quotient map is the underlying map of the Lie quotient map.
  rfl

omit hx in
/-- Ray series of two families whose terms commute pairwise commute. -/
theorem raySeries_lie_raySeries_eq_zero {n' : N} (hn' : n' ∈ d.monoid) (hn0' : n' ≠ 0)
    (hx : ∀ j, x j ∈ ℒ ((j + 1) • n)) {y : ℕ → L} (hy : ∀ j, y j ∈ ℒ ((j + 1) • n'))
    (hxy : ∀ i j, ⁅x i, y j⁆ = 0) (f g : R⟦X⟧) :
    ⁅d.raySeries ℒ x hn hn0 hx f, d.raySeries ℒ y hn' hn0' hy g⁆ = 0 := by
  apply Mei.ModuleFiltration.completion_ext
  intro k
  rw [LieIdeal.projection_bracket, map_zero, ← LieIdeal.completionProjection_apply,
    ← LieIdeal.completionProjection_apply, completionProjection_raySeries,
    completionProjection_raySeries, ← LieHom.map_lie, rayPartialSum_apply,
    rayPartialSum_apply, sum_lie]
  simp [lie_sum, hxy]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The completed label `exp(∑_{j ≥ 0} f_{j+1} x j)` of a power series `f`. -/
def rayExp (f : R⟦X⟧) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (d.raySeries ℒ x hn hn0 hx f)

/-- The ray label is the completed exponential of the ray series. -/
theorem rayExp_def (f : R⟦X⟧) :
    d.rayExp ℒ x hn hn0 hx f = d.completedBCHExp ℒ (d.raySeries ℒ x hn hn0 hx f) := (rfl)

/-- At order `k`, a ray label is the exponential of the partial sum over `j < k`. -/
@[simp]
theorem projection_rayExp (k : ℕ) (f : R⟦X⟧) :
    CompletedGroup.projection k (d.rayExp ℒ x hn hn0 hx f) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ (rayPartialSum x k f)) := by
  rw [rayExp, projection_completedBCHExp, completionProjection_raySeries]

/-- The logarithm of the order-`k` projection of a ray label is its partial sum. -/
theorem log_projection_rayExp (k : ℕ) (f : R⟦X⟧) :
    BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k (d.rayExp ℒ x hn hn0 hx f))
      = (d.degreeIdeal ℒ k).mkQ (rayPartialSum x k f) := by
  rw [projection_rayExp, BCHGroup.log_exp]

/-- The zero series gives the identity label. -/
@[simp]
theorem rayExp_zero : d.rayExp ℒ x hn hn0 hx 0 = 1 := by
  rw [rayExp, map_zero, completedBCHExp_zero]

/-- Negating the series inverts the ray label. -/
@[simp]
theorem rayExp_neg (f : R⟦X⟧) : d.rayExp ℒ x hn hn0 hx (-f) = (d.rayExp ℒ x hn hn0 hx f)⁻¹ := by
  simp only [rayExp_def, map_neg, completedBCHExp_neg]

omit hx in
/-- Ray labels of two families whose terms commute pairwise commute. -/
theorem commute_rayExp {n' : N} (hn' : n' ∈ d.monoid) (hn0' : n' ≠ 0)
    (hx : ∀ j, x j ∈ ℒ ((j + 1) • n)) {y : ℕ → L} (hy : ∀ j, y j ∈ ℒ ((j + 1) • n'))
    (hxy : ∀ i j, ⁅x i, y j⁆ = 0) (f g : R⟦X⟧) :
    Commute (d.rayExp ℒ x hn hn0 hx f) (d.rayExp ℒ y hn' hn0' hy g) := by
  have hyx (i j : ℕ) : ⁅y i, x j⁆ = 0 := by rw [← lie_skew, hxy, neg_zero]
  rw [Commute, SemiconjBy, rayExp_def, rayExp_def,
    ← completedBCHExp_add_of_lie_eq_zero _ _
      (d.raySeries_lie_raySeries_eq_zero ℒ x hn hn0 hn' hn0' hx hy hxy f g),
    ← completedBCHExp_add_of_lie_eq_zero _ _
      (d.raySeries_lie_raySeries_eq_zero ℒ y hn' hn0' hn hn0 hy hx hyx g f), add_comm]

/-- If the terms commute pairwise, ray labels multiply by adding their power series. -/
theorem rayExp_add (hxx : ∀ i j, ⁅x i, x j⁆ = 0) (f g : R⟦X⟧) :
    d.rayExp ℒ x hn hn0 hx (f + g) = d.rayExp ℒ x hn hn0 hx f * d.rayExp ℒ x hn hn0 hx g := by
  simp only [rayExp_def, map_add]
  exact completedBCHExp_add_of_lie_eq_zero _ _
    (d.raySeries_lie_raySeries_eq_zero ℒ x hn hn0 hn hn0 hx hx hxx f g)

/-- The logarithmic coefficient of a ray label in degree `(j+1)n` is `f_{j+1} x j`. -/
@[simp]
theorem logComponent_rayExp_succ_nsmul (f : R⟦X⟧) (j : ℕ) :
    (d.logComponent ℒ (d.rayExp ℒ x hn hn0 hx f) ((j + 1) • n) : L) = coeff (j + 1) f • x j := by
  let k := (d.degree ((j + 1) • n)).toNat
  have hj : j ∈ Finset.range k := Finset.mem_range.mpr (by
    have := d.lt_degree_succ_nsmul hn hn0 j
    omega)
  rw [d.logComponent_eq_decompose ℒ _ (Int.self_le_toNat _)
    (d.log_projection_rayExp ℒ x hn hn0 hx k f).symm, rayPartialSum_apply,
    DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum,
    Finset.sum_eq_single_of_mem j hj]
  · exact DirectSum.decompose_of_mem_same ℒ ((ℒ _).smul_mem _ (hx j))
  · intro i _ hij
    exact DirectSum.decompose_of_mem_ne ℒ ((ℒ _).smul_mem _ (hx i))
      fun h => hij (d.succ_nsmul_injective hn hn0 h)

/-- A ray label lies in the completed subgroup of every supported ray containing `n`. -/
theorem rayExp_mem_completedRaySubgroup {w : SupportedRay d} (hw : n ∈ w.rayDegrees)
    (f : R⟦X⟧) : d.rayExp ℒ x hn hn0 hx f ∈ d.completedRaySubgroup ℒ w := by
  rw [mem_completedRaySubgroup]
  intro k
  rw [d.log_projection_rayExp ℒ x hn hn0 hx k f, ← map_rayLieSubalgebra_mkQ]
  refine ⟨_, ?_, rfl⟩
  rw [rayPartialSum_apply]
  exact Submodule.sum_mem (rayLieSubalgebra ℒ w).toSubmodule fun j _ =>
    le_rayLieSubalgebra ℒ (SupportedRay.succ_nsmul_mem_rayDegrees hw j)
      ((ℒ _).smul_mem _ (hx j))

end Mei.PositiveDegrees
