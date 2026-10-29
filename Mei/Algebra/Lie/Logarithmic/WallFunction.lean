/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.RingTheory.Derivation.Exp
public import Mei.RingTheory.FilteredAlgebra.Exp.Map
public import Mei.RingTheory.Nilpotent.Log

/-!
# Wall functions of tangent tropical vertex labels

Fix a character `m` of the spatial lattice. The allowed degrees tangent to `m` form the
monoid `T = {n ∈ P | m(ρ n) = 0}`, and a coefficient `u = ∑ u_q z^q` on `T` defines the
positive tropical vertex field `u ∂_m = ∑_{q ≠ 0} u_q z^q ∂_m`. On a coefficient algebra
`R[Q]`, when `u.coeff 0 = 0`, this field acts as `u` times the weight derivation
`z^p ↦ m(ρ p) z^p`, and `u` has weight zero. When `u` has positive coefficient order,
the exponential of `u ∂_m` multiplies `z^p` by `exp(m(ρ p) u)` at every finite order.
Completed tangent coefficients of positive order give completed fields, and
the completed label `exp(u ∂_m)` acts on the completed coefficient algebra by the same
formula. For an integral character `n` and a completed tangent series `f` congruent to one,
the label `exp(log(f) ∂_n)` therefore multiplies `z^p` by the unit power `f^{n(ρ p)}`.
These are the function walls of tropical vertex wall-crossing automorphisms; a ray series
along a primitive degree `w` with `n(ρ w) = 0` is the special case of a series supported on
`ℕ w`.

The construction uses `tropicalVertexCoefficientAction`, `AlgFiltration.completedBCHAction`,
`AlgFiltration.completedExp` and `AlgFiltration.completedLog`, and Mei's
`Units.exp_zsmul_log` for the integral powers. The formula
`exp(log(f) ∂_m)(z^p) = z^p f^{m(ρ p)}` is that of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5; see also
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1,
arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (m : Λ →+ R)

/-- The allowed degrees tangent to the character `m`. -/
def tropicalTangentMonoid : AddSubmonoid Γ :=
  d.monoid ⊓ AddMonoidHom.mker (m.comp ρ)

/-- A degree is tangent when it is allowed and killed by `m ∘ ρ`. -/
@[simp]
theorem mem_tropicalTangentMonoid (n : Γ) :
    n ∈ tropicalTangentMonoid d ρ m ↔ n ∈ d.monoid ∧ m (ρ n) = 0 := by
  simp [tropicalTangentMonoid]

/-- Tangent degrees are allowed degrees. -/
theorem tropicalTangentMonoid_le : tropicalTangentMonoid d ρ m ≤ d.monoid :=
  inf_le_left

local notation "T" => tropicalTangentMonoid d ρ m

variable [DecidableEq Γ]

private def tangentFieldValue (q : T) : tropicalVertexLieAlgebra (R := R) d ρ :=
  if hq : (q : Γ) = 0 then 0 else
    ⟨LogarithmicVectorField.single ρ q m, single_mem_tropicalVertexLieAlgebra d ρ
      ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1 hq m
      ((mem_tropicalTangentMonoid d ρ m q).mp q.2).2⟩

/-- The positive tangent field `u ∂_m` of a coefficient `u` supported on tangent degrees.
The constant coefficient is discarded, since degree zero carries no positive field. -/
def tropicalTangentField : R[T] →ₗ[R] tropicalVertexLieAlgebra (R := R) d ρ :=
  (basis T R).constr R (tangentFieldValue d ρ m)

private theorem tropicalTangentField_single' (q : T) (c : R) :
    tropicalTangentField d ρ m (single q c) = c • tangentFieldValue d ρ m q := by
  have h : tropicalTangentField d ρ m (single q 1) = tangentFieldValue d ρ m q :=
    (basis T R).constr_basis R (tangentFieldValue d ρ m) q
  calc
    _ = tropicalTangentField d ρ m (c • single q 1) := by simp
    _ = _ := by rw [map_smul, h]

/-- A nonzero tangent monomial `c z^q` gives the field `c z^q ∂_m`. -/
@[simp]
theorem coe_tropicalTangentField_single {q : T} (hq : (q : Γ) ≠ 0) (c : R) :
    (tropicalTangentField d ρ m (single q c) : LogarithmicVectorField R Γ Λ ρ) =
      LogarithmicVectorField.single ρ q (c • m) := by
  simp [tropicalTangentField_single', tangentFieldValue, hq]

/-- The constant coefficient gives no field. -/
@[simp]
theorem tropicalTangentField_single_zero (c : R) :
    tropicalTangentField d ρ m (single 0 c) = 0 := by
  simp [tropicalTangentField_single', tangentFieldValue]

section Action

variable (Q : AddSubmonoid Γ) (hQ : d.monoid ≤ Q)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T

/-- The inclusion of tangent coefficients into the coefficient monoid algebra. -/
abbrev tropicalTangentInclusion : R[T] →ₐ[R] R[Q] :=
  mapDomainAlgHom R R (AddSubmonoid.inclusion ((tropicalTangentMonoid_le d ρ m).trans hQ))

omit [DecidableEq Γ] in
/-- Tangent coefficients have weight zero for the character `m`. -/
@[simp]
theorem monomialDerivation_zero_tropicalTangentInclusion (u : R[T]) :
    AddMonoidAlgebra.monomialDerivation (0 : Q) (m.comp (ρ.comp Q.subtype))
      (mapDomain (AddSubmonoid.inclusion ((tropicalTangentMonoid_le d ρ m).trans hQ)) u) = 0 := by
  induction u using induction_linear with
  | zero => simp
  | add a b ha hb => simp only [mapDomain_add, map_add, ha, hb, add_zero]
  | single q c =>
    simp [((mem_tropicalTangentMonoid d ρ m q).mp q.2).2]

omit [DecidableEq Γ] in
/-- Including tangent coefficients preserves coefficient order. -/
theorem filtration_ideal_le_comap_tropicalTangentInclusion (k : ℕ) :
    (G).ideal k ≤ ((F).ideal k).comap (tropicalTangentInclusion d ρ m Q hQ) := by
  rw [TropicalVertexCoefficientAction.filtration_ideal,
    TropicalVertexCoefficientAction.filtration_ideal]
  exact (d.monoid.comap (T).subtype).monoidAlgebraIdeal_le_comap_mapDomainRingHom
    (d.degree.comp (T).subtype) (d.monoid.comap Q.subtype) (d.degree.comp Q.subtype)
    (AddSubmonoid.inclusion ((tropicalTangentMonoid_le d ρ m).trans hQ))
    (fun _ hn => hn) (fun _ _ h => h)

omit [DecidableEq Γ] in
/-- A tangent coefficient of positive order has no constant coefficient. -/
theorem coeff_zero_eq_zero_of_mem_filtration_ideal_one {v : R[T]} (hv : v ∈ (G).ideal 1) :
    v.coeff 0 = 0 := by
  have htop : d.monoid.comap (T).subtype = ⊤ := by
    ext q
    simp only [AddSubmonoid.mem_comap, AddSubmonoid.subtype_apply, AddSubmonoid.mem_top,
      iff_true]
    exact ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1
  rw [TropicalVertexCoefficientAction.filtration_ideal, htop,
    AddSubmonoid.mem_monoidAlgebraIdeal_top_iff_of_nonneg
      (fun q : T => d.degree_nonneg ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1)] at hv
  by_contra h
  have hd := hv 0 (Finsupp.mem_support_iff.mpr h)
  simp at hd

/-- The field `u ∂_m` acts as `u` times the weight derivation of `m`, when `u` has no
constant coefficient. -/
theorem tropicalVertexCoefficientAction_tropicalTangentField (u : R[T])
    (hu : u.coeff 0 = 0) :
    tropicalVertexCoefficientAction d ρ Q hQ (tropicalTangentField d ρ m u) =
      tropicalTangentInclusion d ρ m Q hQ u •
        AddMonoidAlgebra.monomialDerivation (0 : Q) (m.comp (ρ.comp Q.subtype)) := by
  rw [← sum_coeff_single u, Finsupp.sum, map_sum, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : (q : Γ) ≠ 0 := by
    rintro h
    have : q = 0 := Subtype.ext h
    subst this
    simp [hu] at hq
  have hqd := ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1
  rw [tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hqd _ (u.coeff q • m)
    (coe_tropicalTangentField_single d ρ m hq0 _).symm,
    AddMonoidAlgebra.monomialDerivation_eq_single_smul]
  have hc : (u.coeff q • m).comp (ρ.comp Q.subtype) = u.coeff q • m.comp (ρ.comp Q.subtype) := by
    ext; simp
  rw [hc, map_smul, smul_comm, ← smul_assoc, smul_single', mul_one]
  simp [AddSubmonoid.inclusion]

end Action

section Completion

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "𝔤" => tropicalVertexLieAlgebra (R := R) d ρ

/-- Tangent coefficients of order above `k` give fields above degree `k`. -/
theorem tropicalTangentField_mem_degreeIdeal {k : ℕ} {v : R[T]} (hv : v ∈ (G).ideal (k + 1)) :
    tropicalTangentField d ρ m v ∈ d.degreeIdeal ℒ k := by
  have htop : d.monoid.comap (T).subtype = ⊤ := by
    ext q
    simp only [AddSubmonoid.mem_comap, AddSubmonoid.subtype_apply, AddSubmonoid.mem_top,
      iff_true]
    exact ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1
  rw [TropicalVertexCoefficientAction.filtration_ideal, htop,
    AddSubmonoid.mem_monoidAlgebraIdeal_top_iff_of_nonneg
      (fun q : T => d.degree_nonneg ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1)] at hv
  rw [← sum_coeff_single v, Finsupp.sum, map_sum]
  refine Submodule.sum_mem (d.degreeIdeal ℒ k).toSubmodule fun q hq => ?_
  by_cases hq0 : (q : Γ) = 0
  · have h0 : q = 0 := Subtype.ext hq0
    rw [h0, tropicalTangentField_single_zero]
    exact zero_mem _
  · refine d.le_degreeIdeal ℒ (n := (q : Γ)) ?_ ?_
    · have hd := hv q hq
      simpa only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, Nat.cast_add,
        Nat.cast_one] using (Int.add_one_le_iff.mp hd)
    · rw [mem_tropicalVertexGrading_iff]
      exact ⟨_, (coe_tropicalTangentField_single d ρ m hq0 _).symm⟩

private def tangentFieldQuotient (k : ℕ) :
    (R[T] ⧸ (G).ideal (k + 1)) →ₗ[R] 𝔤 ⧸ (d.degreeIdeal ℒ k).toSubmodule :=
  (((G).ideal (k + 1)).restrictScalars R).liftQ
      ((d.degreeIdeal ℒ k).toSubmodule.mkQ ∘ₗ tropicalTangentField d ρ m) (by
        intro v hv
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact tropicalTangentField_mem_degreeIdeal d ρ m hv) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((G).ideal (k + 1))).symm.toLinearMap

private theorem tangentFieldQuotient_mk (k : ℕ) (v : R[T]) :
    tangentFieldQuotient d ρ m k (Ideal.Quotient.mk _ v) =
      Submodule.Quotient.mk (tropicalTangentField d ρ m v) := by
  rw [tangentFieldQuotient, LinearMap.comp_apply, ← Ideal.Quotient.mk_eq_mk,
    LinearEquiv.coe_coe, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- The completed tangent field `u ∂_m` of a completed tangent coefficient `u`, as an
element of the completed tropical vertex Lie algebra. -/
def completedTropicalTangentField : (G).completion →ₗ[R] d.completedLie ℒ :=
  (LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)).lift
    (fun k => tangentFieldQuotient d ρ m k ∘ₗ ((G).projectionₐ (R := R) k).toLinearMap) (by
      intro k l h
      apply LinearMap.ext
      intro u
      obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((G).projection l u)
      have hk : (G).projection k u = Ideal.Quotient.mk _ v := by
        rw [← (G).factor_projection h, ← hv]
        rfl
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgFiltration.projectionₐ_apply, ← hv, hk]
      rw [tangentFieldQuotient_mk, tangentFieldQuotient_mk]
      exact ModuleFiltration.transition_mk _ h _)

/-- At order `k`, the completed tangent field is the class of the tangent field of any
representative of the order-`k` coefficient. -/
theorem completionProjection_completedTropicalTangentField (k : ℕ) (u : (G).completion)
    (v : R[T]) (hv : (G).projection k u = Ideal.Quotient.mk _ v) :
    LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k
        (completedTropicalTangentField d ρ m u) =
      (d.degreeIdeal ℒ k).mkQ (tropicalTangentField d ρ m v) := by
  rw [LieIdeal.completionProjection_apply, completedTropicalTangentField,
    ModuleFiltration.projection_lift, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgFiltration.projectionₐ_apply, hv, tangentFieldQuotient_mk]
  rfl

/-- Completing a finite tangent coefficient commutes with forming its tangent field. -/
@[simp]
theorem completedTropicalTangentField_toCompletion (u : R[T]) :
    completedTropicalTangentField d ρ m ((G).toCompletion u) =
      LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
        (tropicalTangentField d ρ m u) := by
  apply ModuleFiltration.completion_ext
  intro k
  simpa only [← LieIdeal.completionProjection_apply] using
    (completionProjection_completedTropicalTangentField d ρ m k _ u
      ((G).projection_toCompletion k u)).trans
      (LieIdeal.completionProjection_toCompletion _ _ k _).symm

end Completion

section Exponential

variable [Algebra ℚ R] (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

open TropicalVertexCoefficientAction

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d T
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ

/-- At finite order, the exponential of `u ∂_m` multiplies a monomial `r z^p` by
`exp(m(ρ p) u)`. -/
theorem quotientExpLieAction_tropicalTangentField (k : ℕ) (u : R[T]) (hu : u ∈ (G).ideal 1)
    (p : Q) (r : R) :
    (F).quotientExpLieAction d ℒ k (tropicalTangentField d ρ m u)
        (Ideal.Quotient.mk _ (single p r)) =
      IsNilpotent.exp (Ideal.Quotient.mk ((F).ideal (k + 1))
          (m (ρ p) • tropicalTangentInclusion d ρ m Q Fact.out u)) *
        Ideal.Quotient.mk _ (single p r) := by
  let δ : Derivation R R[Q] R[Q] :=
    AddMonoidAlgebra.monomialDerivation (0 : Q) (m.comp (ρ.comp Q.subtype))
  have hδ : ∀ a, Ideal.Quotient.mkₐ R ((F).ideal (k + 1)) a = 0 →
      Ideal.Quotient.mkₐ R ((F).ideal (k + 1)) (δ a) = 0 := by
    intro a ha
    have ha' : a ∈ (F).ideal (k + 1) := Ideal.Quotient.eq_zero_iff_mem.mp ha
    rw [TropicalVertexCoefficientAction.filtration_ideal] at ha'
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [TropicalVertexCoefficientAction.filtration_ideal]
    simpa only [Nat.zero_add] using
      (d.monoid.comap Q.subtype).monomialDerivation_mem_monoidAlgebraIdeal
        (d.degree.comp Q.subtype) (n := 0) (zero_mem _) (m.comp (ρ.comp Q.subtype))
        (a := 0) (b := k + 1) (by simp) ha'
  let D : Derivation R (R[Q] ⧸ (F).ideal (k + 1)) (R[Q] ⧸ (F).ideal (k + 1)) :=
    Derivation.liftOfSurjective (f := Ideal.Quotient.mkₐ R ((F).ideal (k + 1)))
      (d := δ) Ideal.Quotient.mk_surjective hδ
  let x := Ideal.Quotient.mk ((F).ideal (k + 1))
    (tropicalTangentInclusion d ρ m Q Fact.out u)
  have hD (a : R[Q]) : D (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (δ a) :=
    Derivation.liftOfSurjective_apply _ hδ a
  have hx : D x = 0 := by
    simp only [x, hD, δ, tropicalTangentInclusion, mapDomainAlgHom_apply,
      monomialDerivation_zero_tropicalTangentInclusion d ρ m Q Fact.out, map_zero]
  have hn : IsNilpotent x := by
    refine ⟨k + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.mul_one] using (F).pow_mem
      (filtration_ideal_le_comap_tropicalTangentInclusion d ρ m Q Fact.out 1 hu) (k + 1)
  have ha : D (Ideal.Quotient.mk _ (single p r)) =
      m (ρ p) • Ideal.Quotient.mk _ (single p r) := by
    rw [hD, AddMonoidAlgebra.monomialDerivation_single, zero_add]
    simp only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply]
    simpa only [Ideal.Quotient.mkₐ_eq_mk, smul_single', smul_eq_mul, mul_comm] using
      map_smul (Ideal.Quotient.mkₐ R ((F).ideal (k + 1))) (m (ρ p)) (single p r)
  have he : (F).quotientLieAction d ℒ k (tropicalTangentField d ρ m u) =
      (x • D).toLinearMap := by
    apply LinearMap.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [AlgFiltration.quotientLieAction_mk, lie_eq,
      tropicalVertexCoefficientAction_tropicalTangentField d ρ m Q _ u
        (coeff_zero_eq_zero_of_mem_filtration_ideal_one d ρ m hu),
      Derivation.smul_apply, smul_eq_mul, map_mul]
    simp only [Derivation.coeFn_coe, Derivation.smul_apply, hD, smul_eq_mul]
    rfl
  rw [AlgFiltration.quotientExpLieAction_apply, he, D.exp_smul_toLinearMap_apply hx hn ha]
  congr 2

omit [DecidableEq Γ] in
/-- Completed tangent coefficients, viewed as completed coefficients. -/
def completedTropicalTangentInclusion : (G).completion →ₐ[R] (F).completion :=
  (G).mapCompletionₐ (F) (tropicalTangentInclusion d ρ m Q Fact.out) id monotone_id
    fun k => filtration_ideal_le_comap_tropicalTangentInclusion d ρ m Q Fact.out (k + 1)

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- Forgetting scalars in the completed tangent inclusion gives the filtered
ring completion map of the monoid inclusion. -/
@[simp]
theorem coe_completedTropicalTangentInclusion :
    (completedTropicalTangentInclusion d ρ m Q : (G).completion →+* (F).completion) =
      (G).mapCompletion (F) (tropicalTangentInclusion d ρ m Q Fact.out : _ →+* _)
        id monotone_id
        (fun k => filtration_ideal_le_comap_tropicalTangentInclusion d ρ m Q Fact.out (k + 1)) := by
  unfold completedTropicalTangentInclusion
  exact (G).coe_mapCompletionₐ (F) (tropicalTangentInclusion d ρ m Q Fact.out)
    id monotone_id _

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- At order `k`, the map of completions is the induced map of coefficient quotients. -/
@[simp]
theorem projection_completedTropicalTangentInclusion (k : ℕ) (u : (G).completion) :
    (F).projection k (completedTropicalTangentInclusion d ρ m Q u) =
      Ideal.quotientMapₐ ((F).ideal (k + 1)) (tropicalTangentInclusion d ρ m Q Fact.out)
        (filtration_ideal_le_comap_tropicalTangentInclusion d ρ m Q Fact.out (k + 1))
        ((G).projection k u) :=
  (G).projection_mapCompletionₐ_of_le (F) (tropicalTangentInclusion d ρ m Q Fact.out)
    id monotone_id _ k k le_rfl u

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- Completing a finite tangent coefficient commutes with its inclusion. -/
@[simp]
theorem completedTropicalTangentInclusion_toCompletion (u : R[T]) :
    completedTropicalTangentInclusion d ρ m Q ((G).toCompletion u) =
      (F).toCompletion (tropicalTangentInclusion d ρ m Q Fact.out u) :=
  (G).mapCompletionₐ_toCompletion (F) _ id monotone_id _ u

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- Completed tangent coefficients of positive order map to positive order. -/
theorem completedTropicalTangentInclusion_mem_completionIdeal_one {u : (G).completion}
    (hu : u ∈ (G).completionIdeal 1) :
    completedTropicalTangentInclusion d ρ m Q u ∈ (F).completionIdeal 1 :=
  (G).mapCompletionₐ_mem_completionIdeal (F) (tropicalTangentInclusion d ρ m Q Fact.out)
    id monotone_id
    (fun k => filtration_ideal_le_comap_tropicalTangentInclusion d ρ m Q Fact.out (k + 1)) 0 hu

/-- **The tangent wall function.** The completed label `exp(u ∂_m)` of a completed tangent
coefficient `u` of positive order multiplies a monomial `r z^p` by `exp(m(ρ p) u)`. -/
theorem completedBCHAction_completedBCHExp_completedTropicalTangentField (u : (G).completion)
    (hu : u ∈ (G).completionIdeal 1) (p : Q) (r : R) :
    (F).completedBCHAction d ℒ (d.completedBCHExp ℒ (completedTropicalTangentField d ρ m u))
        ((F).toCompletion (single p r)) =
      (F).completedExp ⟨m (ρ p) • completedTropicalTangentInclusion d ρ m Q u,
          Submodule.smul_of_tower_mem _ _
            (completedTropicalTangentInclusion_mem_completionIdeal_one d ρ m Q hu)⟩ *
        (F).toCompletion (single p r) := by
  apply (F).completion_ext
  intro k
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((G).projection k u)
  have h0 : (G).projection 0 u = 0 := by
    simpa only [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] using hu
  have hv1 : Ideal.Quotient.mk ((G).ideal (0 + 1)) v = 0 := by
    rw [← h0, ← (G).factor_projection (Nat.zero_le k), ← hv]
    rfl
  rw [AlgFiltration.projection_completedBCHAction, PositiveDegrees.projection_completedBCHExp,
    BCHGroup.log_exp, completionProjection_completedTropicalTangentField d ρ m k u v hv.symm]
  rw [AlgFiltration.projection_toCompletion, map_mul, AlgFiltration.projection_completedExp,
    AlgFiltration.projection_toCompletion]
  rw [LieIdeal.mkQ_apply, AlgFiltration.truncatedExpLieAction_mk,
    quotientExpLieAction_tropicalTangentField d ρ m Q k v (Ideal.Quotient.eq_zero_iff_mem.mp hv1)]
  congr 2
  dsimp only
  have hp : (F).projection k (m (ρ p) • completedTropicalTangentInclusion d ρ m Q u) =
      m (ρ p) • Ideal.Quotient.mk _ (tropicalTangentInclusion d ρ m Q Fact.out v) := by
    rw [Algebra.smul_def, map_mul, AlgFiltration.projection_algebraMap,
      projection_completedTropicalTangentInclusion, ← hv, ← Algebra.smul_def]
    rfl
  rw [hp]
  exact map_smul (Ideal.Quotient.mkₐ R _) _ _

omit [Algebra ℚ R] [DecidableEq Γ] in
/-- A completed tangent coefficient congruent to one is a unit of the coefficient
completion. -/
theorem isUnit_completedTropicalTangentInclusion {f : (G).completion}
    (hf : f - 1 ∈ (G).completionIdeal 1) : IsUnit (completedTropicalTangentInclusion d ρ m Q f) :=
  (F).isUnit_of_sub_one_mem (by
    simpa only [map_sub, map_one] using
      completedTropicalTangentInclusion_mem_completionIdeal_one d ρ m Q hf)

end Exponential

section Integral

variable [Algebra ℚ R] (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)] (n : Λ →+ ℤ)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
open TropicalVertexCoefficientAction

local notation "χ" => AddMonoidHom.comp (Int.castAddHom R) n
local notation "G" =>
  TropicalVertexCoefficientAction.filtration (R := R) d (tropicalTangentMonoid d ρ χ)

/-- **Wall-function formula.** For an integral normal `n` and a completed tangent wall
function `f` congruent to one, the label `exp(log(f) ∂_n)` multiplies a monomial `r z^p` by
`f^{n(ρ p)}`, the power being taken in units. -/
theorem completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
    {f : (G).completion} (hf : f - 1 ∈ (G).completionIdeal 1) (p : Q) (r : R) :
    (F).completedBCHAction d ℒ (d.completedBCHExp ℒ
        (completedTropicalTangentField d ρ χ ((G).completedLog ⟨f, hf⟩)))
        ((F).toCompletion (single p r)) =
      ((isUnit_completedTropicalTangentInclusion d ρ χ Q hf).unit ^ n (ρ p) : (F).completionˣ) *
        (F).toCompletion (single p r) := by
  rw [completedBCHAction_completedBCHExp_completedTropicalTangentField d ρ χ Q _
    ((G).completedLog_mem ⟨f, hf⟩) p r]
  congr 1
  apply (F).completion_ext
  intro k
  set U := (isUnit_completedTropicalTangentInclusion d ρ χ Q hf).unit with hUdef
  have hlog :
      (F).projection k (completedTropicalTangentInclusion d ρ χ Q ((G).completedLog ⟨f, hf⟩)) =
      IsNilpotent.log ((F).projection k (completedTropicalTangentInclusion d ρ χ Q f)) := by
    rw [completedTropicalTangentInclusion, ← AlgHom.coe_toRingHom,
      AlgFiltration.coe_mapCompletionₐ]
    simpa only [AlgFiltration.projection_completedLog] using
      congrArg ((F).projection k)
        ((G).mapCompletion_completedLog (F) (tropicalTangentInclusion d ρ χ Q Fact.out : _ →+* _)
          id monotone_id
          (fun k => filtration_ideal_le_comap_tropicalTangentInclusion d ρ χ Q Fact.out (k + 1))
          (filtration_ideal_le_comap_tropicalTangentInclusion d ρ χ Q Fact.out 1) ⟨f, hf⟩)
  let φ : (F).completion →* R[Q] ⧸ (F).ideal (k + 1) := ((F).projection k).toMonoidHom
  have hU1 : IsNilpotent ((F).projection k (completedTropicalTangentInclusion d ρ χ Q f) - 1) := by
    have h := (F).isNilpotent_projection (by
      simpa only [map_sub, map_one] using
        completedTropicalTangentInclusion_mem_completionIdeal_one d ρ χ Q hf) k
    rwa [map_sub, map_one] at h
  have hu : IsNilpotent ((Units.map φ U : R[Q] ⧸ (F).ideal (k + 1)) - 1) := by
    simpa only [Units.coe_map, hUdef, IsUnit.unit_spec, φ, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass] using hU1
  rw [AlgFiltration.projection_completedExp]
  dsimp only
  rw [AddMonoidHom.comp_apply, Int.coe_castAddHom, Int.cast_smul_eq_zsmul, map_zsmul, hlog]
  have he := Units.exp_zsmul_log (Units.map φ U) hu (n (ρ p))
  rw [← map_zpow, Units.coe_map] at he
  simpa only [Units.coe_map, hUdef, IsUnit.unit_spec, φ, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass] using he

end Integral

end Mei
