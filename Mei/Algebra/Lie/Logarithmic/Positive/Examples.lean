/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Coefficient.NonnegIntegers
public import Mei.Algebra.Lie.Logarithmic.Positive
public import Mei.RingTheory.FilteredAlgebra.Positive.PowerSeries
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Map
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Checks on the specialization `a ↦ 1`

Let `R` be a commutative ring and `a` a polynomial variable. Two checks compare the
specialization `a ↦ 1` for the `t`-adic and the `a`-adic filtrations.

* *The `t`-adic filtration.* Realize `R[a][t]` and `R[t]` as coefficient monoid algebras over
  the nonnegative integers `PositiveDegrees.nonnegIntegers`, with `t` the variable
  `PositiveDegrees.nonnegIntegers.X`. Their positive-increment filtration is the `t`-adic
  filtration (`TropicalVertexCoefficientAction.filtration_nonnegIntegers_eq_ofIdeal`). The
  coefficientwise substitution `a ↦ 1` is a positive specialization `atOne` for the
  subsemirings `ℕ[a][t]` and `ℕ[t]`, an instance of
  `Mei.LogarithmicVectorField.coefficientMonoidPositiveSpecialization`. Its completion map
  sends the positive series `∑ⱼ aʲ tʲ` (`atSeries`, `projection_atSeries`,
  `isPositive_atSeries`) to `∑ⱼ tʲ` (`completionMap_atOne_atSeries`, `projection_tSeries`),
  which is positive for `ℕ[t]` (`isPositive_tSeries`).

* *The `a`-adic filtration.* For the filtration of `R[a]` by the powers of `(a)`, the series
  `∑ⱼ aʲ` (`aSeries`, `projection_aSeries`) is positive for `ℕ[a]` (`isPositive_aSeries`) and
  is the inverse of `1 - a` (`aSeries_mul_one_sub`). A ring homomorphism out of the `a`-adic
  completion sending `a` to `1` has a trivial target (`subsingleton_of_map_X_eq_one`). There
  is no positive specialization with `a ↦ 1` into a filtered ring with nontrivial completion,
  for any chosen subsemirings (`isEmpty_positiveSpecialization_X_eq_one`).

The coefficientwise specializations are those of Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, §8.1 (arXiv:2503.03719v1), for the positivity of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

open TauCeti (AlgFiltration)

noncomputable section

namespace Mei.PositiveSpecialization.Examples

open _root_.AddMonoidAlgebra TauCeti.PositiveDegrees nonnegIntegers

local notation "Q" => nonnegIntegers.monoid

variable (R : Type*) [CommRing R]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := Polynomial R)
  nonnegIntegers Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) nonnegIntegers Q
local notation "𝒫" => RingHom.rangeS (mapRingHom Q (Polynomial.mapRingHom (Nat.castRingHom R)))
local notation "𝒫'" => RingHom.rangeS (mapRingHom Q (Nat.castRingHom R))

section TAdic

/-- The series `∑ⱼ aʲ tʲ` in the `t`-adic completion of `R[a][t]`: the geometric series
evaluated at `a t`. -/
def atSeries : (F).completion :=
  (F).completedAeval (R := R)
    ⟨(F).toCompletion (single (natExponent 1) Polynomial.X),
      ((F).toCompletion_mem_completionIdeal_iff 1 _).mpr
        (TropicalVertexCoefficientAction.single_natExponent_mem_filtration_nonnegIntegers_ideal
          _ 1 _)⟩
    (PowerSeries.mk 1)

/-- The series `∑ⱼ tʲ` in the `t`-adic completion of `R[t]`: the geometric series evaluated
at `t`. -/
def tSeries : (G).completion :=
  (G).completedAeval (R := R)
    ⟨(G).toCompletion (X R), ((G).toCompletion_mem_completionIdeal_iff 1 _).mpr
      (TropicalVertexCoefficientAction.X_mem_filtration_nonnegIntegers_ideal_one R)⟩
    (PowerSeries.mk 1)

/-- At order `k`, the series `∑ⱼ aʲ tʲ` is the class of `∑_{j ≤ k} aʲ tʲ`. -/
theorem projection_atSeries (k : ℕ) :
    (F).projection k (atSeries R) =
      Ideal.Quotient.mk _
        (∑ j ∈ Finset.range (k + 1), single (natExponent j) (Polynomial.X (R := R) ^ j)) := by
  rw [atSeries, AlgFiltration.projection_completedAeval_eq_sum]
  simp [← map_pow]

/-- At order `k`, the series `∑ⱼ tʲ` is the class of `∑_{j ≤ k} tʲ`. -/
theorem projection_tSeries (k : ℕ) :
    (G).projection k (tSeries R) =
      Ideal.Quotient.mk _ (∑ j ∈ Finset.range (k + 1), X R ^ j) := by
  simp only [tSeries, AlgFiltration.projection_completedAeval_eq_sum, map_sum, map_pow,
    PowerSeries.coeff_mk, Pi.one_apply, one_smul, AlgFiltration.projection_toCompletion]

/-- The coefficientwise substitution `a ↦ 1` from `R[a][t]` to `R[t]`. -/
def evalOneMap : (Polynomial R)[Q] →ₐ[R] R[Q] :=
  mapAlgHom Q (Polynomial.aeval (1 : R))

/-- The substitution `a ↦ 1` is the coefficient-monoid map with coefficient map
`Polynomial.aeval 1` and trivial twist. -/
theorem evalOneMap_single (p : Q) (r : Polynomial R) :
    evalOneMap R (single p r) =
      single p (Polynomial.aeval (1 : R) r * (1 : Multiplicative Q →* R) (.ofAdd p)) := by
  simp [evalOneMap]

/-- The substitution `a ↦ 1` maps `ℕ[a][t]` into `ℕ[t]`. -/
theorem evalOneMap_mem_rangeS {x : (Polynomial R)[Q]} (hx : x ∈ 𝒫) : evalOneMap R x ∈ 𝒫' :=
  LogarithmicVectorField.map_mem_rangeS_mapRingHom_coefficientMonoidMap Q
    (Polynomial.aeval (1 : R)) 1 (evalOneMap R) (evalOneMap_single R) _ _
    (fun a => ⟨Polynomial.eval 1 a, by simp [Polynomial.eval_one_map]⟩)
    (fun _ => one_mem _) hx

/-- The substitution `a ↦ 1` as a positive specialization from `R[a][t]` to `R[t]`, for the
`t`-adic filtrations and the subsemirings `ℕ[a][t]` and `ℕ[t]`. -/
def atOne : PositiveSpecialization (F) (G) 𝒫 𝒫' :=
  LogarithmicVectorField.coefficientMonoidPositiveSpecialization nonnegIntegers Q
    (Polynomial.aeval (1 : R)) 1 (evalOneMap R) (evalOneMap_single R) 𝒫 𝒫'
    fun _ => evalOneMap_mem_rangeS R

/-- The underlying ring homomorphism of `atOne` is the substitution `a ↦ 1`. -/
@[simp]
theorem atOne_toRingHom : (atOne R).toRingHom = evalOneMap R :=
  LogarithmicVectorField.coefficientMonoidPositiveSpecialization_toRingHom ..

/-- The substitution `a ↦ 1` is filtered for the `t`-adic filtrations with the identity
cutoff modulus. -/
theorem filtration_ideal_le_comap_atOne (k : ℕ) :
    (F).ideal (id k + 1) ≤ ((G).ideal (k + 1)).comap (atOne R).toRingHom := by
  rw [atOne_toRingHom]
  exact LogarithmicVectorField.filtration_ideal_le_comap_coefficientMonoidMap nonnegIntegers Q
    (Polynomial.aeval (1 : R)) 1 (evalOneMap R) (evalOneMap_single R) (k + 1)

/-- With the `t`-adic filtrations, the specialization `a ↦ 1` sends `∑ⱼ aʲ tʲ` to `∑ⱼ tʲ`. -/
theorem completionMap_atOne_atSeries : (atOne R).completionMap (atSeries R) = tSeries R := by
  have hψ (r : R) : (atOne R).toRingHom (algebraMap R _ r) = algebraMap R _ (RingHom.id R r) := by
    rw [atOne_toRingHom, RingHom.id_apply]
    exact (evalOneMap R).commutes r
  rw [(atOne R).completionMap_eq_mapCompletion id monotone_id (filtration_ideal_le_comap_atOne R),
    atSeries, AlgFiltration.mapCompletion_completedAeval _ _ (RingHom.id R) _ hψ _ _ _
      (filtration_ideal_le_comap_atOne R 0), PowerSeries.map_id, id_eq, tSeries]
  refine congrArg (fun x => (G).completedAeval x (PowerSeries.mk 1)) (Subtype.ext ?_)
  simp [AlgFiltration.mapCompletion_toCompletion, evalOneMap, X_def]

/-- The series `∑ⱼ aʲ tʲ` is positive for `ℕ[a][t]`. -/
theorem isPositive_atSeries : (F).IsPositive 𝒫 (atSeries R) := by
  rw [atSeries]
  refine AlgFiltration.IsPositive.completedAeval (AlgFiltration.isPositive_toCompletion
    (RingHom.mem_rangeS.mpr ⟨single (natExponent 1) Polynomial.X, by simp⟩)) fun i => ?_
  rw [PowerSeries.coeff_mk, Pi.one_apply, map_one]
  exact one_mem _

/-- The series `∑ⱼ tʲ`, the image of `∑ⱼ aʲ tʲ` under `a ↦ 1`, is positive for `ℕ[t]`. -/
theorem isPositive_tSeries : (G).IsPositive 𝒫' (tSeries R) :=
  completionMap_atOne_atSeries R ▸ (atOne R).map_isPositive (isPositive_atSeries R)

end TAdic

section AAdic

local notation "𝔄" => Ideal.algFiltration (Ideal.span {(Polynomial.X : Polynomial R)})

/-- The variable `a` lies in the first term of the `a`-adic filtration of `R[a]`. -/
theorem X_mem_ideal_one : Polynomial.X ∈ (𝔄).ideal 1 := by
  simp

/-- The series `∑ⱼ aʲ` in the completion of `R[a]` for the `a`-adic filtration: the geometric
series evaluated at `a`. -/
def aSeries : (𝔄).completion :=
  (𝔄).completedAeval (R := R)
    ⟨(𝔄).toCompletion Polynomial.X, ((𝔄).toCompletion_mem_completionIdeal_iff 1 _).mpr
      (X_mem_ideal_one R)⟩
    (PowerSeries.mk 1)

/-- At order `k`, the series `∑ⱼ aʲ` is the class of `∑_{j ≤ k} aʲ`. -/
theorem projection_aSeries (k : ℕ) :
    (𝔄).projection k (aSeries R) =
      Ideal.Quotient.mk _ (∑ j ∈ Finset.range (k + 1), Polynomial.X (R := R) ^ j) := by
  simp only [aSeries, AlgFiltration.projection_completedAeval_eq_sum, map_sum, map_pow,
    PowerSeries.coeff_mk, Pi.one_apply, one_smul, AlgFiltration.projection_toCompletion]

/-- In the `a`-adic completion, `∑ⱼ aʲ` is the inverse of `1 - a`. -/
theorem aSeries_mul_one_sub : aSeries R * (1 - (𝔄).toCompletion Polynomial.X) = 1 := by
  have h := congrArg ((𝔄).completedAeval (R := R)
    ⟨_, ((𝔄).toCompletion_mem_completionIdeal_iff 1 _).mpr (X_mem_ideal_one R)⟩)
    (PowerSeries.mk_one_mul_one_sub_eq_one R)
  rw [map_mul, map_sub, map_one, AlgFiltration.completedAeval_X] at h
  rwa [aSeries]

/-- The series `∑ⱼ aʲ` is positive for `ℕ[a]`. -/
theorem isPositive_aSeries :
    (𝔄).IsPositive (Polynomial.mapRingHom (Nat.castRingHom R)).rangeS (aSeries R) := by
  rw [aSeries]
  exact AlgFiltration.IsPositive.completedAeval (AlgFiltration.isPositive_toCompletion
    (RingHom.mem_rangeS.mpr ⟨Polynomial.X, Polynomial.map_X _⟩)) fun i => by simp

/-- A ring homomorphism out of the `a`-adic completion of `R[a]` sending `a` to `1` has a
trivial target. -/
theorem subsingleton_of_map_X_eq_one {T : Type*} [Ring T] (Ψ : (𝔄).completion →+* T)
    (hΨ : Ψ ((𝔄).toCompletion Polynomial.X) = 1) : Subsingleton T := by
  have h := congrArg Ψ (aSeries_mul_one_sub R)
  rw [map_mul, map_sub, map_one, hΨ, sub_self, mul_zero] at h
  exact subsingleton_of_zero_eq_one h

/-- For the `a`-adic filtration of `R[a]`, there is no positive specialization with `a ↦ 1`
into a filtered ring with nontrivial completion, for any chosen subsemirings. -/
theorem isEmpty_positiveSpecialization_X_eq_one {C : Type*} [Ring C] (H : AlgFiltration C)
    [Nontrivial H.completion] (P : Subsemiring (Polynomial R)) (P' : Subsemiring C) :
    IsEmpty {φ : PositiveSpecialization (𝔄) H P P' // φ.toRingHom Polynomial.X = 1} := by
  refine ⟨fun ⟨φ, hφ⟩ => not_subsingleton H.completion ?_⟩
  exact subsingleton_of_map_X_eq_one R φ.completionMap
    (by rw [φ.completionMap_toCompletion, hφ, map_one])

end AAdic

end Mei.PositiveSpecialization.Examples
