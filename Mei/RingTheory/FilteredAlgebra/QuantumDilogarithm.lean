/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
public import Mei.RingTheory.PowerSeries.QuantumDilogarithm

/-!
# Quantum dilogarithm conjugation in filtered completions

In an associative filtered algebra, a scalar commutation factor between an element
and a positive-order generator determines conjugation by the quantum dilogarithm
of that generator. Positive and negative even powers of the parameter give finite
products of linear factors and their inverses, respectively.

We evaluate the formal rescaling identities of `Units.quantumDilogarithm` using
`AlgFiltration.completedAeval_conj`. The formulas follow Nakanishi, *Pentagon
relation in quantum cluster scattering diagrams*, §2.3, equations (2.14) and (2.21),
arXiv:2202.01588v7.
-/

public section

noncomputable section

open scoped PowerSeries

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)
  (x : F.completionIdeal 1) (y : F.completion) (q : Rˣ)
  (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))

/-- A positive even commutation factor gives a finite product of linear factors.
The factors are ordered by increasing index in the associative target algebra. -/
theorem completedAeval_quantumDilogarithm_conj_of_nonneg (r : ℕ)
    (hy : SemiconjBy y (((q : R) ^ (2 * r)) • (x : F.completion)) x) :
    F.completedAeval x (Units.quantumDilogarithm q hq) * y *
        F.completedAeval x (PowerSeries.invOfUnit (Units.quantumDilogarithm q hq) 1) =
      y * ((List.range r).map fun j =>
        1 + ((q : R) ^ (2 * j + 1)) • (x : F.completion)).prod := by
  have h := F.completedAeval_conj x y _ hy (Units.quantumDilogarithmUnit q hq)
  simp only [Units.coe_quantumDilogarithmUnit, Units.coe_quantumDilogarithmUnit_inv] at h
  have heval := congrArg (F.completedAeval x)
    (Units.rescale_pow_quantumDilogarithm_mul_inv q hq r)
  refine h.trans (congrArg (fun t => y * t) (heval.trans ?_))
  have hprod := List.prod_toFinset (fun j : ℕ =>
    (1 + PowerSeries.C ((q : R) ^ (2 * j + 1)) * PowerSeries.X : R⟦X⟧))
    (List.nodup_range : (List.range r).Nodup)
  rw [List.toFinset_range] at hprod
  refine (congrArg (F.completedAeval x) hprod).trans ?_
  simp [map_list_prod, List.map_map, Function.comp_def, Algebra.smul_def]

/-- A negative even commutation factor gives a finite product of inverse linear factors.
Every factor is a unit, being the evaluation of a series with constant coefficient one. -/
theorem completedAeval_quantumDilogarithm_conj_of_nonpos (r : ℕ)
    (hy : SemiconjBy y (((↑q⁻¹ : R) ^ (2 * r)) • (x : F.completion)) x) :
    F.completedAeval x (Units.quantumDilogarithm q hq) * y *
        F.completedAeval x (PowerSeries.invOfUnit (Units.quantumDilogarithm q hq) 1) =
      y * ((List.range r).map fun j =>
        Ring.inverse (1 + ((↑q⁻¹ : R) ^ (2 * j + 1)) • (x : F.completion))).prod := by
  have h := F.completedAeval_conj x y _ hy (Units.quantumDilogarithmUnit q hq)
  simp only [Units.coe_quantumDilogarithmUnit, Units.coe_quantumDilogarithmUnit_inv] at h
  have heval := congrArg (F.completedAeval x)
    (Units.rescale_inv_pow_quantumDilogarithm_mul_inv q hq r)
  refine h.trans (congrArg (fun t => y * t) (heval.trans ?_))
  have hprod := List.prod_toFinset (fun j : ℕ => PowerSeries.invOfUnit
    (1 + PowerSeries.C ((↑q⁻¹ : R) ^ (2 * j + 1)) * PowerSeries.X : R⟦X⟧) 1)
    (List.nodup_range : (List.range r).Nodup)
  rw [List.toFinset_range] at hprod
  refine (congrArg (F.completedAeval x) hprod).trans ?_
  simp [map_list_prod, List.map_map, Function.comp_def, Algebra.smul_def]

end Mei.AlgFiltration
