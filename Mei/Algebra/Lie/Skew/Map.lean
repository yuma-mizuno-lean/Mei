/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Ray

/-!
# Maps of skew Lie algebras

An additive map of exponent groups and a scalar `c` induce the map
`X_n ↦ c X_(f n)` when `β(n,m) = c β'(f n,f m)`. A positive degree map
then transports positive skew algebras and their completed ray labels.
This allows identities to be transported from a normalized skew form.
-/

public section

noncomputable section

namespace Mei.SkewLieAlgebra

variable {R Γ Γ' : Type*} [CommRing R] [AddCommGroup Γ] [AddCommGroup Γ']
  (β : Γ →ₗ[ℤ] Γ →ₗ[ℤ] R) (hβ : β.IsAlt)
  (β' : Γ' →ₗ[ℤ] Γ' →ₗ[ℤ] R) (hβ' : β'.IsAlt)
  (f : Γ →+ Γ') (c : R) (h : ∀ n m, β n m = c * β' (f n) (f m))

/-- The skew Lie map `X_n ↦ c X_(f n)` for a scalar-compatible map of forms. -/
def map : SkewLieAlgebra β hβ →ₗ⁅R⁆ SkewLieAlgebra β' hβ' :=
  { (Finsupp.lsum R fun n => c • single β' hβ' (f n)).comp
      (toFinsupp β hβ).toLinearMap with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      induction x using induction_on β hβ with
      | h0 => simp
      | hs n r =>
        induction y using induction_on β hβ with
        | h0 => simp
        | hs m s =>
          simp only [single_bracket_single, toFinsupp_single, Finsupp.lsum_single,
            LinearMap.smul_apply, map_add, ← map_smul, h]
          congr 1
          ring
        | ha y z hy hz => simp only [lie_add, _root_.map_add, hy, hz]
      | ha x z hx hz => simp only [add_lie, _root_.map_add, hx, hz] }

/-- The skew map is the linear extension of its values on generators. -/
theorem map_apply (x : SkewLieAlgebra β hβ) :
    map β hβ β' hβ' f c h x =
      (Finsupp.lsum R fun n => c • single β' hβ' (f n)) (toFinsupp β hβ x) := (rfl)

/-- The scalar-compatible skew map on a homogeneous generator. -/
@[simp]
theorem map_single (n : Γ) (r : R) :
    map β hβ β' hβ' f c h (single β hβ n r) = single β' hβ' (f n) (c * r) := by
  rw [map_apply, toFinsupp_single, Finsupp.lsum_single, LinearMap.smul_apply,
    ← _root_.map_smul, smul_eq_mul]

variable {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  (T : PositiveDegreeMap d e)
  (hT : ∀ n m, β n m = c * β' (T n) (T m))

private theorem map_mem_positive (x : positiveLieAlgebra β hβ d) :
    map β hβ β' hβ' T.toAddMonoidHom c hT x.val ∈ positiveLieAlgebra β' hβ' e := by
  have hle : positiveLieAlgebra β hβ d ≤
      (positiveLieAlgebra β' hβ' e).comap (map β hβ β' hβ' T.toAddMonoidHom c hT) := by
    rw [positiveLieAlgebra_def]
    apply (supportedLieSubalgebra_le_iff (grade β hβ) _ _).mpr
    rintro n ⟨hn, hn0⟩ x hx
    obtain ⟨r, rfl⟩ := (mem_grade_iff β hβ n x).mp hx
    rw [LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_comap, map_single]
    classical
    rw [mem_positiveLieAlgebra_iff]
    intro m hm
    rw [toFinsupp_single, Finsupp.single_apply, ite_eq_right_iff]
    rintro rfl
    exact (hm.elim (fun h => h (T.map_mem hn)) (T.map_ne_zero hn hn0)).elim
  exact hle x.property

private def positiveMap : positiveLieAlgebra β hβ d →ₗ⁅R⁆ positiveLieAlgebra β' hβ' e :=
  { ((map β hβ β' hβ' T.toAddMonoidHom c hT).toLinearMap.comp
        (positiveLieAlgebra β hβ d).incl.toLinearMap).codRestrict _
          (map_mem_positive β hβ β' hβ' c T hT) with
      map_lie' {x y} := Subtype.ext ((map β hβ β' hβ' T.toAddMonoidHom c hT).map_lie x.val y.val) }

private theorem coe_positiveMap_apply (x : positiveLieAlgebra β hβ d) :
    (positiveMap β hβ β' hβ' c T hT x).val =
      map β hβ β' hβ' T.toAddMonoidHom c hT x.val := (rfl)

/-- A positive degree map compatible with the forms transports the positive skew Lie algebra. -/
def gradedMap : GradedLieHom T (positiveGrading β hβ d) (positiveGrading β' hβ' e) where
  toLieHom := positiveMap β hβ β' hβ' c T hT
  map_mem {n x} hx := by
    obtain ⟨r, hr⟩ := (mem_grade_iff β hβ n x.val).mp
      ((mem_positiveGrading_iff β hβ d n x).mp hx)
    apply (mem_positiveGrading_iff β' hβ' e (T n) _).mpr
    apply (mem_grade_iff β' hβ' (T n) _).mpr
    refine ⟨c * r, ?_⟩
    rw [coe_positiveMap_apply, ← hr, map_single]

/-- Forgetting positive support recovers the ambient scalar-compatible map. -/
@[simp]
theorem coe_gradedMap_apply (x : positiveLieAlgebra β hβ d) :
    (gradedMap β hβ β' hβ' c T hT x).val =
      map β hβ β' hβ' T.toAddMonoidHom c hT x.val := (rfl)

variable [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ']

/-- A truncated skew map transports a projected ray label by scaling its power series.
The source order must cover both the target order and the degree map's modulus. -/
theorem truncatedMap_gradedMap_projection_rayExp {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)
    (g : PowerSeries R) (k a : ℕ) (hka : k ≤ a) (hma : T.modulus k ≤ a) :
    ((gradedMap β hβ β' hβ' c T hT).truncatedMap k hma).bchGroupMap
        (CompletedGroup.projection a (rayExp β hβ hn hn0 g)) =
      CompletedGroup.projection k
        (rayExp β' hβ' (T.map_mem hn) (T.map_ne_zero hn hn0) (c • g)) := by
  rw [projection_rayExp, projection_rayExp, LieHom.bchGroupMap_exp]
  congr 1
  rw [LieIdeal.mkQ_apply, GradedLieHom.truncatedMap_mk]
  have hgen (j : ℕ) : gradedMap β hβ β' hβ' c T hT
      (rayGenerator β hβ hn hn0 j (PowerSeries.coeff (j + 1) g)) =
      rayGenerator β' hβ' (T.map_mem hn) (T.map_ne_zero hn hn0) j
        (PowerSeries.coeff (j + 1) (c • g)) := by
    apply Subtype.ext
    simp only [coe_gradedMap_apply, coe_rayGenerator, map_single, _root_.map_nsmul,
      PowerSeries.coeff_smul, smul_eq_mul]
  have hsum : gradedMap β hβ β' hβ' c T hT (rayPartialSum β hβ hn hn0 a g) =
      rayPartialSum β' hβ' (T.map_mem hn) (T.map_ne_zero hn hn0) a (c • g) := by
    simp only [rayPartialSum_apply, _root_.map_sum, hgen]
  rw [hsum]
  exact (Submodule.Quotient.eq _).mpr
    (rayPartialSum_sub_mem β' hβ' (T.map_mem hn) (T.map_ne_zero hn hn0) hka (c • g))

end Mei.SkewLieAlgebra
