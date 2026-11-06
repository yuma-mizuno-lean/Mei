/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon

/-!
# Type `A₂` with isolated indices for the principal BLM extension

Let `B` be an adapted basis of a skew lattice datum, `ℓ_i` positive integers at the unfrozen
indices, and `i₁, i₂` two unfrozen indices. Suppose `ℓ_{i₁} = ℓ_{i₂} = 1`,
`d_{i₂} {e_{i₁}, e_{i₂}} = d_{i₁} {e_{i₁}, e_{i₂}} = 1`, and every other unfrozen basis vector `e_i`
pairs to zero with all unfrozen basis vectors. Then the principal BLM extension
(`SkewLatticeDatum.AdaptedBasis.principalBLMExtension`) is a polynomial input of type `A₂` with
isolated indices at the unfrozen indices `a_{i₁}, a_{i₂}`
(`SkewLatticeDatum.AdaptedBasis.principalBLMExtension_isTypeA₂WithIsolated`): the multiplicities
`ℓ_i` and the multipliers `d_i` at the isolated indices are arbitrary. The extension carries a
polynomial input for every adapted basis, so this applies to degenerate forms, and it identifies
the exponents of the extension, `w_i(a_j) = d_j {e_i, e_j}`, with the pairings of the original
basis.

The extension is the realization of the principal initial walls of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix B (arXiv:1411.1394v2), as a polynomial input of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1
(arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  [DecidableEq ι] [Fintype ι] [Nonempty ι] (ℓ : B.unfrozenIndex → ℕ+)

variable {i₁ i₂ : B.unfrozenIndex}

/-- **The principal BLM extension of type `A₂` with isolated indices.** If `ℓ_{i₁} = ℓ_{i₂} = 1`,
`d_{i₂} {e_{i₁}, e_{i₂}} = d_{i₁} {e_{i₁}, e_{i₂}} = 1`, and every other unfrozen basis vector `e_i`
pairs to zero with all unfrozen basis vectors, the principal BLM extension is a polynomial input of
type `A₂` with isolated indices at the unfrozen indices `a_{i₁}, a_{i₂}`. The multipliers `d_i` and
the multiplicities `ℓ_i` at the isolated indices are arbitrary. -/
theorem principalBLMExtension_isTypeA₂WithIsolated (hℓ₁ : ℓ i₁ = 1) (hℓ₂ : ℓ i₂ = 1)
    (h₁ : (B.multiplier i₂ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1)
    (h₂ : (B.multiplier i₁ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1)
    (hiso : ∀ i : B.unfrozenIndex, i ≠ i₁ → i ≠ i₂ → ∀ j : B.unfrozenIndex,
      D.form (B.basis i) (B.basis j) = 0) :
    (B.principalBLMExtension ℓ).IsTypeA₂WithIsolated (B.principalBLMUnfrozenEquiv ℓ i₁)
      (B.principalBLMUnfrozenEquiv ℓ i₂) where
  multiplicity_fst := by simp [hℓ₁]
  multiplicity_snd := by simp [hℓ₂]
  multiplier_mul_form_fst := by
    rw [principalBLMExtension_multiplier_mul_form, hℓ₁, h₁]
    simp
  multiplier_mul_form_snd := by
    rw [(B.principalBLMDatum ℓ).form_swap, mul_neg, principalBLMExtension_multiplier_mul_form,
      hℓ₂, D.form_swap, mul_neg, mul_neg, h₂]
    simp
  form_eq_zero i hi₁ hi₂ j := by
    obtain ⟨i, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective i
    obtain ⟨j, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective j
    have h := principalBLMExtension_multiplier_mul_form B ℓ i j
    rw [hiso i (fun he => hi₁ (he ▸ rfl)) (fun he => hi₂ (he ▸ rfl)) j, mul_zero,
      mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast
      ((B.principalBLMBasis ℓ).multiplier_pos _).ne')

end Mei.SkewLatticeDatum.AdaptedBasis
