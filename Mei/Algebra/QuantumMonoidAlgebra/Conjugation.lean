/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.RingTheory.FilteredAlgebra.PowerSeries

/-!
# Quantum ray conjugation in completed coefficient algebras

Unit scalar series evaluated at a positive-degree quantum monomial act by conjugation
on the degree completion of any nonnegative coefficient monoid. Moving a monomial
past a ray series rescales the series by `q^(2β(n,p))`.
All identities hold in the actual coefficient completion and hence in each quotient.

The construction uses `AlgFiltration.completedAeval`,
`QuantumMonoidAlgebra.monomial_semiconjBy`, and the completed semiconjugacy
evaluation identity. The formulas follow Nakanishi, *Pentagon relation in quantum
cluster scattering diagrams*, §2.3, equations (2.14) and (2.21), arXiv:2202.01588v7.
-/

public section

noncomputable section

open scoped PowerSeries

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
  (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)

local notation "F" => positiveFiltration q β P δ hδ
local notation "ι" => AlgFiltration.toCompletionₐ (R := R) F
local notation "z" => (fun p : P => ι (positiveMonomial q β P p))

/-- A quantum monomial of positive degree lies in the first completed ideal. -/
theorem completedMonomial_mem_first (n : P) (hn : 0 < δ n) :
    z n ∈ (F).completionIdeal 1 := by
  simp only [AlgFiltration.toCompletionₐ_apply, (F).toCompletion_mem_completionIdeal_iff]
  have h := (smul_positiveMonomial_mem_positiveFiltration_iff q β P δ hδ 1 n (1 : R)).mpr
    (Or.inr (by omega))
  simpa only [one_smul] using h

variable (n : P) (hn : 0 < δ n)

local notation "x" => (Subtype.mk (z n)
  (completedMonomial_mem_first q β P δ hδ n hn) : AlgFiltration.completionIdeal F 1)

/-- A completed unit ray series conjugates each allowed monomial by its rescaling ratio.
The coefficient monoid can contain nonzero degree-zero exponents. -/
theorem completedAeval_conj_monomial (hβ : β.IsAlt) (p : P) (G : R⟦X⟧ˣ) :
    (F).completedAeval x (G : R⟦X⟧) * z p *
        (F).completedAeval x (↑(G⁻¹) : R⟦X⟧) =
      z p * (F).completedAeval x
        (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (G : R⟦X⟧) *
          (↑(G⁻¹) : R⟦X⟧)) := by
  apply (F).completedAeval_conj
  have h : SemiconjBy (positiveMonomial q β P p)
      (((q ^ (2 * β n p) : Rˣ) : R) • positiveMonomial q β P n)
      (positiveMonomial q β P n) := by
    apply Subtype.ext
    simpa only [SemiconjBy, Subalgebra.coe_mul, Subalgebra.coe_smul,
      coe_positiveMonomial] using
      monomial_semiconjBy q β hβ n p
  have hc := congrArg ι h
  simp only [SemiconjBy] at hc ⊢
  simpa only [map_mul, AlgHom.map_smul_of_tower] using hc

end Mei.QuantumMonoidAlgebra
