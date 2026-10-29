/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Skew.Grading
public import Mei.Algebra.Lie.BCH.Ray.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series on a ray of the positive skew Lie algebra

Let `n` be a nonzero allowed degree of positive degree data on the exponent group of a skew
Lie algebra. A formal power series `f = ∑ f_j Tʲ` defines the completed Lie element
`∑_{j ≥ 1} f_j X_{jn}`; its order-`k` projection is the class of the finite sum over
`j ≤ k`, since `δ(jn) = j δ(n) > k` for `j > k`. The constant coefficient is ignored.
These elements pairwise commute, so their completed exponentials `rayExp f` form a
homomorphic image of the additive group of power series. Every `rayExp f` lies in the
completed ray subgroup of the supported ray through `n`, and its logarithmic coefficient
in degree `jn`, `j ≥ 1`, is `f_j X_{jn}`.

Such ray labels are the wall-crossing automorphisms of cluster scattering diagrams, for
example the dilogarithm elements `Ψ[n]` of Gross–Hacking–Keel–Kontsevich, *Canonical bases
for cluster algebras*, §1.1, arXiv:1411.1394v2.

The construction uses `ModuleFiltration.lift` for the compatible finite sums and
`PositiveDegrees.completedBCHExp` for the levelwise exponentials; coefficients are read by
`PositiveDegrees.logComponent_eq_decompose`.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt) {d : PositiveDegrees Γ}
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)

local notation "𝔤" => positiveLieAlgebra β hβ d
local notation "ℒ" => positiveGrading β hβ d
local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

include hn hn0

/-- The positive skew generator `c X_{(j+1)n}` on the ray of a nonzero allowed degree `n`. -/
def rayGenerator (j : ℕ) : R →ₗ[R] 𝔤 where
  toFun c := ⟨single β hβ ((j + 1) • n) c, by
    classical
    rw [mem_positiveLieAlgebra_iff]
    intro m hm
    rw [toFinsupp_single, Finsupp.single_apply, ite_eq_right_iff]
    rintro rfl
    exact (hm.elim (· (d.monoid.nsmul_mem hn (j + 1))) (d.succ_nsmul_ne_zero hn hn0 j)).elim⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp]
theorem coe_rayGenerator (j : ℕ) (c : R) :
    (rayGenerator β hβ hn hn0 j c : SkewLieAlgebra β hβ) = single β hβ ((j + 1) • n) c :=
  (rfl)

/-- The ray generator in degree `(j+1)n` is homogeneous of that degree. -/
theorem rayGenerator_mem (j : ℕ) (c : R) : rayGenerator β hβ hn hn0 j c ∈ ℒ ((j + 1) • n) :=
  (mem_positiveGrading_iff β hβ d _ _).mpr ((mem_grade_iff β hβ _ _).mpr ⟨c, rfl⟩)

/-- Generators on one ray commute. -/
@[simp]
theorem rayGenerator_bracket_rayGenerator (i j : ℕ) (b c : R) :
    ⁅rayGenerator β hβ hn hn0 i b, rayGenerator β hβ hn hn0 j c⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, coe_rayGenerator, coe_rayGenerator, ← natCast_zsmul,
    ← natCast_zsmul]
  exact single_zsmul_bracket_single_zsmul β hβ n _ _ b c

/-- The finite sum `∑_{j < k} f_{j+1} X_{(j+1)n}`. -/
def rayPartialSum (k : ℕ) : R⟦X⟧ →ₗ[R] 𝔤 :=
  ∑ j ∈ Finset.range k, (rayGenerator β hβ hn hn0 j).comp (coeff (j + 1))

theorem rayPartialSum_apply (k : ℕ) (f : R⟦X⟧) :
    rayPartialSum β hβ hn hn0 k f =
      ∑ j ∈ Finset.range k, rayGenerator β hβ hn hn0 j (coeff (j + 1) f) := by
  simp [rayPartialSum]

variable [DecidableEq Γ]

/-- Terms beyond order `k` lie in the degree ideal above `k`. -/
theorem rayPartialSum_sub_mem {k l : ℕ} (h : k ≤ l) (f : R⟦X⟧) :
    rayPartialSum β hβ hn hn0 l f - rayPartialSum β hβ hn hn0 k f ∈ d.degreeIdeal ℒ k := by
  rw [rayPartialSum_apply, rayPartialSum_apply, ← Finset.sum_range_add_sum_Ico _ h,
    add_sub_cancel_left]
  refine Submodule.sum_mem (d.degreeIdeal ℒ k).toSubmodule fun j hj => ?_
  apply d.le_degreeIdeal ℒ (lt_of_le_of_lt _ (d.lt_degree_succ_nsmul hn hn0 j))
    (rayGenerator_mem β hβ hn hn0 j _)
  exact_mod_cast (Finset.mem_Ico.mp hj).1

/-- The completed Lie element `∑_{j ≥ 1} f_j X_{jn}` of a power series `f`. -/
def raySeries : R⟦X⟧ →ₗ[R] d.completedLie ℒ :=
  (F).lift (fun k => (d.degreeIdeal ℒ k).toSubmodule.mkQ ∘ₗ rayPartialSum β hβ hn hn0 k) (by
    intro k l h
    ext f
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply,
      Mei.ModuleFiltration.transition_mk]
    exact (Submodule.Quotient.eq _).mpr (rayPartialSum_sub_mem β hβ hn hn0 h f))

/-- At order `k`, the ray series is the class of its partial sum over `j < k`. -/
@[simp]
theorem completionProjection_raySeries (k : ℕ) (f : R⟦X⟧) :
    LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k
        (raySeries β hβ hn hn0 f) =
      (d.degreeIdeal ℒ k).mkQ (rayPartialSum β hβ hn hn0 k f) := by
  rw [LieIdeal.completionProjection_apply, raySeries, Mei.ModuleFiltration.projection_lift]
  -- The submodule quotient map is the underlying map of the Lie quotient map.
  rfl

/-- Ray series pairwise commute. -/
@[simp]
theorem raySeries_bracket_raySeries (f g : R⟦X⟧) :
    ⁅raySeries β hβ hn hn0 f, raySeries β hβ hn hn0 g⁆ = 0 := by
  apply Mei.ModuleFiltration.completion_ext
  intro k
  rw [LieIdeal.projection_bracket, map_zero, ← LieIdeal.completionProjection_apply,
    ← LieIdeal.completionProjection_apply, completionProjection_raySeries,
    completionProjection_raySeries, ← LieHom.map_lie, rayPartialSum_apply,
    rayPartialSum_apply, sum_lie]
  simp [lie_sum]

variable [Algebra ℚ R]

/-- The completed label `exp(∑_{j ≥ 1} f_j X_{jn})` of a power series `f`. -/
def rayExp (f : R⟦X⟧) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (raySeries β hβ hn hn0 f)

theorem rayExp_def (f : R⟦X⟧) :
    rayExp β hβ hn hn0 f = d.completedBCHExp ℒ (raySeries β hβ hn hn0 f) := (rfl)

/-- At order `k`, a ray label is the exponential of the partial sum over `j < k`. -/
@[simp]
theorem projection_rayExp (k : ℕ) (f : R⟦X⟧) :
    CompletedGroup.projection k (rayExp β hβ hn hn0 f) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ (rayPartialSum β hβ hn hn0 k f)) := by
  rw [rayExp, PositiveDegrees.projection_completedBCHExp, completionProjection_raySeries]

@[simp]
theorem rayExp_zero : rayExp β hβ hn hn0 0 = 1 := by
  rw [rayExp, map_zero, PositiveDegrees.completedBCHExp_zero]

/-- Ray labels multiply by adding their power series. -/
theorem rayExp_add (f g : R⟦X⟧) :
    rayExp β hβ hn hn0 (f + g) = rayExp β hβ hn hn0 f * rayExp β hβ hn hn0 g := by
  simp only [rayExp_def, map_add]
  exact PositiveDegrees.completedBCHExp_add_of_lie_eq_zero _ _
    (raySeries_bracket_raySeries β hβ hn hn0 f g)

@[simp]
theorem rayExp_neg (f : R⟦X⟧) : rayExp β hβ hn hn0 (-f) = (rayExp β hβ hn hn0 f)⁻¹ := by
  simp only [rayExp_def, map_neg, PositiveDegrees.completedBCHExp_neg]

theorem rayExp_zsmul (m : ℤ) (f : R⟦X⟧) :
    rayExp β hβ hn hn0 (m • f) = rayExp β hβ hn hn0 f ^ m := by
  simp only [rayExp_def, map_zsmul, PositiveDegrees.completedBCHExp_zsmul]

/-- Ray labels of one degree commute. -/
theorem commute_rayExp (f g : R⟦X⟧) :
    Commute (rayExp β hβ hn hn0 f) (rayExp β hβ hn hn0 g) := by
  rw [Commute, SemiconjBy, ← rayExp_add, ← rayExp_add, add_comm]

/-- Logarithm of the order-`k` projection, for reading coefficients. -/
private theorem log_projection_rayExp (k : ℕ) (f : R⟦X⟧) :
    (d.degreeIdeal ℒ k).mkQ (rayPartialSum β hβ hn hn0 k f) =
      BCHGroup.log (L := d.truncatedLie ℒ k)
        (CompletedGroup.projection k (rayExp β hβ hn hn0 f)) := by
  rw [projection_rayExp, BCHGroup.log_exp]

/-- The logarithmic coefficient of a ray label in degree `(j+1)n` is `f_{j+1} X_{(j+1)n}`. -/
@[simp]
theorem logComponent_rayExp_succ_nsmul (f : R⟦X⟧) (j : ℕ) :
    (d.logComponent ℒ (rayExp β hβ hn hn0 f) ((j + 1) • n) : 𝔤) =
      rayGenerator β hβ hn hn0 j (coeff (j + 1) f) := by
  let k := (d.degree ((j + 1) • n)).toNat
  have hj : j ∈ Finset.range k := Finset.mem_range.mpr (by
    have := d.lt_degree_succ_nsmul hn hn0 j
    omega)
  rw [d.logComponent_eq_decompose ℒ _ (Int.self_le_toNat _)
    (log_projection_rayExp β hβ hn hn0 k f), rayPartialSum_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_eq_single_of_mem j hj]
  · exact DirectSum.decompose_of_mem_same ℒ (rayGenerator_mem β hβ hn hn0 j _)
  · intro i _ hij
    exact DirectSum.decompose_of_mem_ne ℒ (rayGenerator_mem β hβ hn hn0 i _)
      fun h => hij (d.succ_nsmul_injective hn hn0 h)

/-- Off the positive multiples of `n`, a ray label has no logarithmic coefficient. -/
theorem logComponent_rayExp_eq_zero_of_forall_ne (f : R⟦X⟧) {m : Γ}
    (hm : ∀ j : ℕ, (j + 1) • n ≠ m) :
    d.logComponent ℒ (rayExp β hβ hn hn0 f) m = 0 := by
  let k := (d.degree m).toNat
  rw [d.logComponent_eq_decompose ℒ _ (Int.self_le_toNat _)
    (log_projection_rayExp β hβ hn hn0 k f), rayPartialSum_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply]
  exact Finset.sum_eq_zero fun j _ => Subtype.ext <|
    (DirectSum.decompose_of_mem_ne ℒ (rayGenerator_mem β hβ hn hn0 j _) (hm j)).trans
      (ZeroMemClass.coe_zero _).symm

/-- A ray label lies in the completed subgroup of the supported ray through `n`. -/
theorem rayExp_mem_completedRaySubgroup {w : SupportedRay d} (hw : n ∈ w.rayDegrees)
    (f : R⟦X⟧) : rayExp β hβ hn hn0 f ∈ d.completedRaySubgroup ℒ w := by
  rw [PositiveDegrees.mem_completedRaySubgroup]
  intro k
  rw [← log_projection_rayExp, ← PositiveDegrees.map_rayLieSubalgebra_mkQ]
  refine ⟨_, ?_, rfl⟩
  rw [rayPartialSum_apply]
  exact Submodule.sum_mem (rayLieSubalgebra ℒ w).toSubmodule fun j _ =>
    le_rayLieSubalgebra ℒ (SupportedRay.succ_nsmul_mem_rayDegrees hw j)
      (rayGenerator_mem β hβ hn hn0 j _)

end Mei.SkewLieAlgebra
