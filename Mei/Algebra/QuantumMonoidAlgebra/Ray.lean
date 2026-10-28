/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Hom
public import Mei.RingTheory.PowerSeries.Monomial

/-!
# Coefficientwise conjugation along quantum rays

The formal parameter records the multiple of the ray exponent. Thus evaluating
`G(T)` at `z^n T` represents a series supported on the ray through `n`, and
left multiplication by `z^p` represents support on `p + ℕ n`.

For `r = β(n,p)`, conjugation by a unit series `G(z^n T)` has right multiplier
`G(q^(2r) z^n T) / G(z^n T)`. If the scalar ratio has coefficient `h_j`,
the corresponding quantum monomial coefficient is `q^(-jr) h_j`.
These are identities of formal series; no topology or choice of truncation is used.
Compatible coefficient and exponent maps commute with the ray evaluation.

We use `PowerSeries.evalMonomial_conj`, `QuantumMonoidAlgebra.monomial_mul`
and `monomial_pow`. The formula follows Nakanishi, *Pentagon relation in quantum
cluster scattering diagrams*, §2.3, equations (2.14) and (2.21).
-/

public section

noncomputable section

open scoped PowerSeries

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (hβ : β.IsAlt) (n p : Γ)

include hβ

/-- Moving a quantum ray generator past a monomial rescales it by `q^(2β(n,p))`. -/
theorem monomial_semiconjBy :
    SemiconjBy (monomial q β p)
      (((q ^ (2 * β n p) : Rˣ) : R) • monomial q β n) (monomial q β n) := by
  unfold SemiconjBy
  rw [mul_smul_comm, monomial_mul, monomial_mul, smul_smul,
    ← Units.val_mul, ← zpow_add, ← hβ.neg_eq n p]
  congr 2
  · congr 1
    omega
  · exact add_comm p n

/-- A unit series on a quantum ray conjugates a monomial by the scalar rescaling ratio. -/
theorem evalMonomial_conj (G : R⟦X⟧ˣ) :
    PowerSeries.evalMonomial (monomial q β n) (G : R⟦X⟧) *
        PowerSeries.C (monomial q β p) *
        PowerSeries.evalMonomial (monomial q β n) (↑(G⁻¹) : R⟦X⟧) =
      PowerSeries.C (monomial q β p) * PowerSeries.evalMonomial (monomial q β n)
        (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (G : R⟦X⟧) * (↑(G⁻¹) : R⟦X⟧)) :=
  PowerSeries.evalMonomial_conj _ _ _ (monomial_semiconjBy q β hβ n p) G

/-- Left multiplication by a quantum monomial contributes the factor `q^(-jβ(n,p))`
to the coefficient at exponent `p + j • n`. -/
theorem coeff_C_mul_evalMonomial (H : R⟦X⟧) (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.C (monomial q β p) *
      PowerSeries.evalMonomial (monomial q β n) H) =
        (((q ^ (-((j : ℤ) * β n p)) : Rˣ) : R) * PowerSeries.coeff j H) •
          monomial q β (p + j • n) := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_evalMonomial,
    monomial_pow q β hβ, mul_smul_comm, monomial_mul, smul_smul]
  simp [← hβ.neg_eq n p, mul_comm]

/-- The coefficientwise quantum ray conjugation formula, with its ordering scalar. -/
theorem coeff_evalMonomial_conj (G : R⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff j
      (PowerSeries.evalMonomial (monomial q β n) (G : R⟦X⟧) *
        PowerSeries.C (monomial q β p) *
        PowerSeries.evalMonomial (monomial q β n) (↑(G⁻¹) : R⟦X⟧)) =
      (((q ^ (-((j : ℤ) * β n p)) : Rˣ) : R) *
        PowerSeries.coeff j
          (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (G : R⟦X⟧) * (↑(G⁻¹) : R⟦X⟧))) •
        monomial q β (p + j • n) := by
  rw [evalMonomial_conj q β hβ, coeff_C_mul_evalMonomial q β hβ]

omit hβ in
/-- Compatible quantum maps commute with formal evaluation on rays. -/
theorem map_evalMonomial {S Γ' : Type*} [CommRing S] [AddCommGroup Γ']
    {q' : Sˣ} {β' : LinearMap.BilinForm ℤ Γ'} (φ : R →+* S) (f : Γ →+ Γ')
    (h : ∀ a b, Units.map φ.toMonoidHom (q ^ β a b) = q' ^ β' (f a) (f b))
    (G : R⟦X⟧) :
    PowerSeries.map (map φ f h) (PowerSeries.evalMonomial (monomial q β n) G) =
      PowerSeries.evalMonomial (monomial q' β' (f n)) (PowerSeries.map φ G) := by
  simpa only [map_monomial] using
    PowerSeries.map_evalMonomial φ (map φ f h) (map_algebraMap φ f h) (monomial q β n) G

end Mei.QuantumMonoidAlgebra
