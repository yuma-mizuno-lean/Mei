/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.Principal
public import Mathlib.Data.Nat.Cast.Field

/-!
# The principal BLM extension of an adapted polynomial input

Let `(N, N_uf, N°, {,})` be a skew lattice datum with an adapted basis `(e_j)_{j ∈ ι}`, unfrozen
indices `I_uf` and multipliers `d_j`, and let `ℓ_i` be positive integers at the unfrozen indices.
The initial walls `(e_i⊥ × (N_uf)_ℝ, 1 + ∑_s a_{i,s} (q^{e_i})^s)` of the principal realization
(Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and Appendix B,
arXiv:1411.1394v2) live on the principal lattice `L_pr = M° × N_uf`, `M° = Hom(N°, ℤ)`, and need
not satisfy the injectivity assumption (8.3) of Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams* (arXiv:2503.03719v1), for instance when the form is zero.

This file constructs a skew lattice datum on `N^B = ℤ^{ι ⊔ I_uf}` with basis vectors `a_j`,
`j ∈ ι`, and `c_i`, `i ∈ I_uf`, together with a polynomial input in the sense of BLM,
Definitions 8.1 and 8.2, with the same unfrozen indices and multiplicities. The unfrozen
vectors are the `a_i`, `i ∈ I_uf`; the `c_i` are frozen. With `φ : N^B → N°`, `a_j ↦ d_j e_j`,
`c_i ↦ 0`, the form is a multiple `c > 0` (for nonempty `ι`) of
`{φ x, φ y} + ∑_i d_i (x_{a_i} y_{c_i} - x_{c_i} y_{a_i})`: on the `a_j` it is `c` times
`{d_j e_j, d_{j'} e_{j'}}`, it pairs `a_i` with `c_i` by `c d_i > 0`, and it vanishes on every
other pair involving a `c_i`. The frozen diagonal block makes the injectivity assumption hold
for every datum, including degenerate and zero forms: for the zero form with `I_uf` nonempty,
which admits no polynomial input on `N` itself (`BLMPolynomialInput.isEmpty_of_form_eq_zero`),
the extension still carries one. With `Λ = ∏_{i ∈ I_uf} d_i`, the multipliers of the
`a_i`, `i ∈ I_uf`, are proportional to `Λ ℓ_i / d_i` and those of the frozen `a_j` and of the
`c_i` to `Λ`, all divided by their greatest common divisor `g` so that they are coprime, and
the scale is `c = g / Λ`. These choices give the relation `ℓ_i w_i = d^B_{a_i} {a_i, -}` of
BLM's Definition 8.2 and both integrality conditions of the extension.

The space lattice `Hom(N^B, ℤ)` is identified with `L_pr = M° × N_uf` by restriction along
`N° → N^B`, `d_j e_j ↦ a_j`, and the coordinates at the `c_i`, read in the unfrozen basis
(`principalBLMSpaceEquiv`). Under this identification the exponent `w_i` of the initial wall at
`i` is the principal exponent `r(e_i) = ({e_i, -}|_{N°}, e_i)`
(`principalBLMSpaceEquiv_principalBLMExponent`), and evaluation at the initial primitive normal
`a_i` is the principal normal `κ(e_i) ν_{e_i}` (`principalNormal_principalBLMSpaceEquiv`).

## Main declarations

* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMDatum`: the skew lattice datum on `N^B`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMBasis`: its adapted basis `(a_j, c_i)`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMExtension`: the polynomial input on it with
  multiplicities `ℓ_i` and exponents `w_i`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMSpaceEquiv`: `Hom(N^B, ℤ) ≃ M° × N_uf`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMSpaceEquiv_principalBLMExponent`: `w_i = r(e_i)`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalNormal_principalBLMSpaceEquiv`: the initial
  primitive normals `a_i` are the principal normals `κ(e_i) ν_{e_i}`.
* `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMForm_principalBLMInclusion`,
  `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMForm_single_inl_single_inr`,
  `Mei.SkewLatticeDatum.AdaptedBasis.principalBLMForm_single_inr_single_inr`: the values of the
  form on basis vectors.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open Module

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} (B : D.AdaptedBasis ι)

local notation "Nᴮ" => (ι ⊕ B.unfrozenIndex) →₀ ℤ

section Lattice

/-- The map `φ : N^B → N°` sending `a_j` to `d_j e_j` and every `c_i` to `0`. -/
def principalBLMProjection : Nᴮ →ₗ[ℤ] D.sublattice :=
  Finsupp.linearCombination ℤ (Sum.elim B.sublatticeBasis 0)

@[simp]
theorem principalBLMProjection_single_inl (j : ι) (c : ℤ) :
    B.principalBLMProjection (Finsupp.single (.inl j) c) = c • B.sublatticeBasis j := by
  simp [principalBLMProjection]

@[simp]
theorem principalBLMProjection_single_inr (i : B.unfrozenIndex) (c : ℤ) :
    B.principalBLMProjection (Finsupp.single (.inr i) c) = 0 := by
  simp [principalBLMProjection]

/-- The inclusion `N° → N^B`, `d_j e_j ↦ a_j`. -/
def principalBLMInclusion : D.sublattice →ₗ[ℤ] Nᴮ :=
  Finsupp.lmapDomain ℤ ℤ Sum.inl ∘ₗ B.sublatticeBasis.repr.toLinearMap

@[simp]
theorem principalBLMInclusion_sublatticeBasis (j : ι) :
    B.principalBLMInclusion (B.sublatticeBasis j) = Finsupp.single (.inl j) 1 := by
  simp [principalBLMInclusion]

/-- The inclusion of `N°` has vanishing coordinates at the `c_i`. -/
@[simp]
theorem principalBLMInclusion_apply_inr (m : D.sublattice) (i : B.unfrozenIndex) :
    B.principalBLMInclusion m (.inr i) = 0 := by
  simp [principalBLMInclusion, Finsupp.mapDomain_of_notMem_range]

/-- The projection `φ` is a retraction of the inclusion of `N°`. -/
@[simp]
theorem principalBLMProjection_principalBLMInclusion (m : D.sublattice) :
    B.principalBLMProjection (B.principalBLMInclusion m) = m := by
  have h : B.principalBLMProjection ∘ₗ B.principalBLMInclusion = LinearMap.id :=
    B.sublatticeBasis.ext fun j => by simp
  exact LinearMap.congr_fun h m

/-- The exponent `w_i ∈ Hom(N^B, ℤ)` of the initial wall at an unfrozen index `i`:
`w_i(x) = {e_i, φ x} + x_{c_i}`. -/
def principalBLMExponent (i : B.unfrozenIndex) : Module.Dual ℤ Nᴮ :=
  D.principalCharacter ⟨B.basis i, B.basis_mem_unfrozen i⟩ ∘ₗ B.principalBLMProjection +
    Finsupp.lapply (.inr i)

theorem principalBLMExponent_apply (i : B.unfrozenIndex) (x : Nᴮ) :
    B.principalBLMExponent i x =
      D.principalCharacter ⟨B.basis i, B.basis_mem_unfrozen i⟩ (B.principalBLMProjection x) +
        x (.inr i) :=
  (rfl)

@[simp]
theorem cast_principalBLMExponent_apply (i : B.unfrozenIndex) (x : Nᴮ) :
    (B.principalBLMExponent i x : ℚ) =
      D.form (B.basis i) (B.principalBLMProjection x) + x (.inr i) := by
  simp [principalBLMExponent_apply]

/-- The identification `Hom(N^B, ℤ) ≃ M° × N_uf` of the space lattice of the extension with the
principal lattice: a functional `w` goes to its restriction along `N° → N^B` and to
`∑_i w(c_i) e_i`. -/
def principalBLMSpaceEquiv :
    Module.Dual ℤ Nᴮ ≃ₗ[ℤ] Module.Dual ℤ D.sublattice × D.unfrozen :=
  (Finsupp.llift ℤ ℤ ℤ (ι ⊕ B.unfrozenIndex)).symm ≪≫ₗ
    LinearEquiv.sumArrowLequivProdArrow ι B.unfrozenIndex ℤ ℤ ≪≫ₗ
    (B.sublatticeBasis.constr ℤ).prodCongr B.unfrozenBasis.equivFun.symm

/-- The character coordinate of `principalBLMSpaceEquiv` is restriction along `N° → N^B`. -/
@[simp]
theorem principalBLMSpaceEquiv_apply_fst (w : Module.Dual ℤ Nᴮ) :
    (B.principalBLMSpaceEquiv w).1 = w ∘ₗ B.principalBLMInclusion :=
  B.sublatticeBasis.ext fun j => by simp [principalBLMSpaceEquiv]

/-- The unfrozen coordinate of `principalBLMSpaceEquiv` is `∑_i w(c_i) e_i`. -/
@[simp]
theorem principalBLMSpaceEquiv_apply_snd (w : Module.Dual ℤ Nᴮ) :
    (B.principalBLMSpaceEquiv w).2 =
      ∑ i, w (Finsupp.single (.inr i) 1) • B.unfrozenBasis i := by
  simp [principalBLMSpaceEquiv, Basis.equivFun_symm_apply]

/-- The exponent of the initial wall at `i` is the principal exponent
`r(e_i) = ({e_i, -}|_{N°}, e_i)`. -/
@[simp]
theorem principalBLMSpaceEquiv_principalBLMExponent (i : B.unfrozenIndex) :
    B.principalBLMSpaceEquiv (B.principalBLMExponent i) =
      D.principalEmbedding ⟨B.basis i, B.basis_mem_unfrozen i⟩ := by
  classical
  refine Prod.ext (LinearMap.ext fun m => by simp [principalBLMExponent_apply]) ?_
  rw [principalBLMSpaceEquiv_apply_snd, Finset.sum_eq_single i]
  · ext
    simp [principalBLMExponent_apply]
  · intro k _ hk
    simp [principalBLMExponent_apply, hk]
  · simp

/-- Evaluation at the initial primitive normal `a_i` is the principal normal `κ(e_i) ν_{e_i}`
under `principalBLMSpaceEquiv`. -/
theorem principalNormal_principalBLMSpaceEquiv [Module.Free ℤ N] (i : B.unfrozenIndex)
    (w : Module.Dual ℤ Nᴮ) :
    D.principalNormal ⟨B.basis i, B.basis_mem_unfrozen i⟩ (B.principalBLMSpaceEquiv w) =
      w (Finsupp.single (.inl i) 1) := by
  have h : (D.sublattice.toAddSubgroup.rayVector (B.basis i) : D.sublattice) =
      B.sublatticeBasis i :=
    Subtype.ext (by simp)
  simp [h]

end Lattice

section Form

variable [DecidableEq ι] (ℓ : B.unfrozenIndex → ℕ+)

local notation "Λ" => ∏ i ∈ B.unfrozenIndex, B.multiplier i

/-- The multipliers of the extension before the common normalization: `Λ ℓ_i / d_i` at `a_i`
for unfrozen `i`, and `Λ` at the frozen `a_j` and at the `c_i`, where `Λ = ∏_{i ∈ I_uf} d_i`. -/
private def premultiplier : ι ⊕ B.unfrozenIndex → ℕ
  | .inl j => if h : j ∈ B.unfrozenIndex then Λ / B.multiplier j * ℓ ⟨j, h⟩ else Λ
  | .inr _ => Λ

omit [DecidableEq ι] in
private theorem prod_multiplier_pos : 0 < Λ :=
  Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (B.multiplier_pos i).ne')

private theorem premultiplier_pos (b : ι ⊕ B.unfrozenIndex) : 0 < premultiplier B ℓ b := by
  rcases b with j | i
  · by_cases hj : j ∈ B.unfrozenIndex
    · simp only [premultiplier, hj, ↓reduceDIte]
      exact Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (prod_multiplier_pos B)
        (Finset.dvd_prod_of_mem _ hj)) (B.multiplier_pos j)) (ℓ _).pos
    · simpa [premultiplier, hj] using prod_multiplier_pos B
  · exact prod_multiplier_pos B

private theorem premultiplier_div_mul_multiplier (i : B.unfrozenIndex) :
    (premultiplier B ℓ (.inl i) : ℚ) / Λ * B.multiplier i = ℓ i := by
  have hd : (B.multiplier i : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos i).ne'
  have hΛ : ((Λ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (prod_multiplier_pos B).ne'
  simp only [premultiplier, i.2, ↓reduceDIte, Nat.cast_mul,
    Nat.cast_div (Finset.dvd_prod_of_mem _ i.2) hd]
  field_simp

private theorem premultiplier_eq_of_ne (b : ι ⊕ B.unfrozenIndex)
    (hb : ∀ i : B.unfrozenIndex, b ≠ .inl i) : premultiplier B ℓ b = Λ := by
  rcases b with j | i
  · have hj : j ∉ B.unfrozenIndex := fun hj => hb ⟨j, hj⟩ rfl
    simp [premultiplier, hj]
  · rfl

variable [Fintype ι]

private theorem gcd_premultiplier_ne_zero (b : ι ⊕ B.unfrozenIndex) :
    Finset.univ.gcd (premultiplier B ℓ) ≠ 0 := fun h =>
  (premultiplier_pos B ℓ b).ne' (Finset.gcd_eq_zero_iff.mp h b (Finset.mem_univ b))

/-- The multipliers of the adapted basis `(a_j, c_i)` of the extension, coprime by
construction. -/
def principalBLMMultiplier (b : ι ⊕ B.unfrozenIndex) : ℕ :=
  premultiplier B ℓ b / Finset.univ.gcd (premultiplier B ℓ)

theorem principalBLMMultiplier_pos (b : ι ⊕ B.unfrozenIndex) :
    0 < B.principalBLMMultiplier ℓ b :=
  Nat.div_pos (Nat.le_of_dvd (premultiplier_pos B ℓ b) (Finset.gcd_dvd (Finset.mem_univ b)))
    (Nat.pos_of_ne_zero (gcd_premultiplier_ne_zero B ℓ b))

/-- The scale `c` of the form of the extension relative to `{,}` on `N°`; it is positive as soon
as `ι` is nonempty (`principalBLMScale_pos`). -/
def principalBLMScale : ℚ :=
  ((Finset.univ.gcd (premultiplier B ℓ) : ℕ) : ℚ) / Λ

theorem principalBLMScale_pos [Nonempty ι] : 0 < B.principalBLMScale ℓ := by
  have j := Classical.arbitrary ι
  have h := gcd_premultiplier_ne_zero B ℓ (.inl j)
  have := prod_multiplier_pos B
  unfold principalBLMScale
  positivity

private theorem cast_principalBLMMultiplier_mul_principalBLMScale (b : ι ⊕ B.unfrozenIndex) :
    (B.principalBLMMultiplier ℓ b : ℚ) * B.principalBLMScale ℓ = premultiplier B ℓ b / Λ := by
  have hg : ((Finset.univ.gcd (premultiplier B ℓ) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast gcd_premultiplier_ne_zero B ℓ b
  rw [principalBLMMultiplier, principalBLMScale,
    Nat.cast_div (Finset.gcd_dvd (Finset.mem_univ b)) hg]
  field_simp

/-- At an unfrozen `a_i`, the multiplier and the scale satisfy `d^B_{a_i} c = ℓ_i / d_i`. -/
theorem cast_principalBLMMultiplier_inl_mul_principalBLMScale (i : B.unfrozenIndex) :
    (B.principalBLMMultiplier ℓ (.inl i) : ℚ) * B.principalBLMScale ℓ = ℓ i / B.multiplier i := by
  have hd : (B.multiplier i : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos i).ne'
  rw [cast_principalBLMMultiplier_mul_principalBLMScale, ← premultiplier_div_mul_multiplier B ℓ i]
  field_simp

/-- At the frozen `a_j` and at the `c_i`, the multiplier is the inverse of the scale. -/
theorem cast_principalBLMMultiplier_mul_principalBLMScale_of_ne (b : ι ⊕ B.unfrozenIndex)
    (hb : ∀ i : B.unfrozenIndex, b ≠ .inl i) :
    (B.principalBLMMultiplier ℓ b : ℚ) * B.principalBLMScale ℓ = 1 := by
  rw [cast_principalBLMMultiplier_mul_principalBLMScale, premultiplier_eq_of_ne B ℓ b hb,
    div_self (Nat.cast_ne_zero.mpr (prod_multiplier_pos B).ne')]

/-- The skew form of the extension:
`c ({φ x, φ y} + ∑_i d_i (x_{a_i} y_{c_i} - x_{c_i} y_{a_i}))` with the scale
`c = principalBLMScale`. -/
def principalBLMForm : Nᴮ →ₗ[ℤ] Nᴮ →ₗ[ℤ] ℚ :=
  B.principalBLMScale ℓ • (D.form.compl₁₂ (D.sublattice.subtype ∘ₗ B.principalBLMProjection)
      (D.sublattice.subtype ∘ₗ B.principalBLMProjection) +
    ∑ i : B.unfrozenIndex, (B.multiplier i : ℚ) •
      ((LinearMap.mul ℤ ℚ).compl₁₂ ((Algebra.linearMap ℤ ℚ) ∘ₗ Finsupp.lapply (.inl i))
          ((Algebra.linearMap ℤ ℚ) ∘ₗ Finsupp.lapply (.inr i)) -
        (LinearMap.mul ℤ ℚ).compl₁₂ ((Algebra.linearMap ℤ ℚ) ∘ₗ Finsupp.lapply (.inr i))
          ((Algebra.linearMap ℤ ℚ) ∘ₗ Finsupp.lapply (.inl i))))

theorem principalBLMForm_apply (x y : Nᴮ) :
    B.principalBLMForm ℓ x y = B.principalBLMScale ℓ *
      (D.form (B.principalBLMProjection x) (B.principalBLMProjection y) +
        ∑ i : B.unfrozenIndex, (B.multiplier i : ℚ) *
          (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))) := by
  simp [principalBLMForm, mul_add]

theorem principalBLMForm_isAlt : (B.principalBLMForm ℓ).IsAlt := fun x => by
  simp [principalBLMForm_apply, mul_comm]

/-- The form pairs `a_i`, `i ∈ I_uf`, with `x` by `c d_i w_i(x)`. -/
theorem principalBLMForm_single_inl (i : B.unfrozenIndex) (y : Nᴮ) :
    B.principalBLMForm ℓ (Finsupp.single (.inl i) 1) y =
      B.principalBLMScale ℓ * B.multiplier i * B.principalBLMExponent i y := by
  simp [principalBLMForm_apply, Finsupp.single_apply]
  ring

/-- The form pairs `c_i` with `y` by `-c d_i y_{a_i}`. -/
theorem principalBLMForm_single_inr (i : B.unfrozenIndex) (y : Nᴮ) :
    B.principalBLMForm ℓ (Finsupp.single (.inr i) 1) y =
      -(B.principalBLMScale ℓ * B.multiplier i * y (.inl i)) := by
  simp [principalBLMForm_apply, Finsupp.single_apply]
  ring

/-- On `N°`, the form of the extension is the multiple `c {,}` of the original form. -/
@[simp]
theorem principalBLMForm_principalBLMInclusion (m m' : D.sublattice) :
    B.principalBLMForm ℓ (B.principalBLMInclusion m) (B.principalBLMInclusion m') =
      B.principalBLMScale ℓ * D.form m m' := by
  simp [principalBLMForm_apply]

/-- The form pairs `a_j` with `c_i` by `c d_i` when `j = i`, and by `0` otherwise; in particular
it vanishes on the frozen `a_j` against the `c_i`. -/
@[simp]
theorem principalBLMForm_single_inl_single_inr (j : ι) (i : B.unfrozenIndex) :
    B.principalBLMForm ℓ (Finsupp.single (.inl j) 1) (Finsupp.single (.inr i) 1) =
      if j = i then B.principalBLMScale ℓ * B.multiplier i else 0 := by
  rw [← neg_neg (B.principalBLMForm ℓ _ _), (B.principalBLMForm_isAlt ℓ).neg,
    principalBLMForm_single_inr, neg_neg]
  by_cases h : j = i <;> simp [h, eq_comm]

/-- The form vanishes on pairs of the `c_i`. -/
@[simp]
theorem principalBLMForm_single_inr_single_inr (i i' : B.unfrozenIndex) :
    B.principalBLMForm ℓ (Finsupp.single (.inr i) 1) (Finsupp.single (.inr i') 1) = 0 := by
  simp [principalBLMForm_single_inr]

/-- The integrality of the extension form on `a_i`, `i ∈ I_uf`, against the multiples
`d^B_b b` of the basis vectors. -/
private theorem exists_int_principalBLMForm_single_inl (i : B.unfrozenIndex)
    (b : ι ⊕ B.unfrozenIndex) : ∃ k : ℤ, B.principalBLMForm ℓ (Finsupp.single (.inl i) 1)
      (B.principalBLMMultiplier ℓ b • Finsupp.single b 1) = k := by
  rw [principalBLMForm_single_inl, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    show ∀ x y z w : ℚ, x * y * (z * w) = z * x * y * w by intros; ring,
    cast_principalBLMMultiplier_mul_principalBLMScale]
  by_cases hb : ∃ j : B.unfrozenIndex, b = .inl j
  · obtain ⟨j, rfl⟩ := hb
    obtain ⟨k, hk⟩ := D.integral_unfrozen_inf_sublattice (B.basis j)
      (B.multiplier i • B.basis i)
      ⟨nsmul_mem (B.basis_mem_unfrozen i) _, B.nsmul_basis_mem_sublattice i⟩
    rw [map_nsmul, nsmul_eq_mul, D.form_swap] at hk
    have hw : (B.principalBLMExponent i (Finsupp.single (.inl j) 1) : ℚ) =
        B.multiplier j * D.form (B.basis i) (B.basis j) := by
      simp
    refine ⟨-(ℓ j * k), ?_⟩
    rw [hw, show ∀ x y z w : ℚ, x * y * (z * w) = x * z * (y * w) by intros; ring,
      premultiplier_div_mul_multiplier]
    push_cast
    rw [← hk]
    ring
  · simp only [not_exists] at hb
    rw [← cast_principalBLMMultiplier_mul_principalBLMScale,
      cast_principalBLMMultiplier_mul_principalBLMScale_of_ne B ℓ b hb, one_mul]
    exact ⟨B.multiplier i * B.principalBLMExponent i (Finsupp.single b 1), by push_cast; rfl⟩

/-- The integrality of the extension form against the multiples `d^B_{a_i} a_i`,
`i ∈ I_uf`. -/
private theorem exists_int_principalBLMForm_smul_single_inl (i : B.unfrozenIndex)
    (b : ι ⊕ B.unfrozenIndex) : ∃ k : ℤ, B.principalBLMForm ℓ (Finsupp.single b 1)
      (B.principalBLMMultiplier ℓ (.inl i) • Finsupp.single (.inl i) 1) = k := by
  refine ⟨-(ℓ i * B.principalBLMExponent i (Finsupp.single b 1)), ?_⟩
  rw [map_nsmul, nsmul_eq_mul, ← neg_neg (B.principalBLMForm ℓ _ _),
    (B.principalBLMForm_isAlt ℓ).neg, principalBLMForm_single_inl]
  push_cast
  rw [← premultiplier_div_mul_multiplier B ℓ i, ← cast_principalBLMMultiplier_mul_principalBLMScale]
  ring

/-- The skew lattice datum of the extension on `N^B`: unfrozen sublattice spanned by the `a_i`,
`i ∈ I_uf`, finite-index sublattice spanned by the `d^B_b b` for the multipliers
`principalBLMMultiplier`, and the form `principalBLMForm`. -/
def principalBLMDatum : SkewLatticeDatum Nᴮ :=
  SkewLatticeDatum.ofBasis Finsupp.basisSingleOne (B.unfrozenIndex.map .inl)
    (B.principalBLMMultiplier ℓ) (B.principalBLMForm ℓ) (B.principalBLMMultiplier_pos ℓ)
    (B.principalBLMForm_isAlt ℓ)
    (by
      simp only [Finset.mem_map, Function.Embedding.inl_apply, forall_exists_index, and_imp,
        Finsupp.coe_basisSingleOne]
      rintro _ i hi rfl b
      exact exists_int_principalBLMForm_single_inl B ℓ ⟨i, hi⟩ b)
    (by
      simp only [Finset.mem_map, Function.Embedding.inl_apply, forall_exists_index, and_imp,
        Finsupp.coe_basisSingleOne]
      rintro _ i hi rfl b
      exact exists_int_principalBLMForm_smul_single_inl B ℓ ⟨i, hi⟩ b)

@[simp]
theorem principalBLMDatum_form : (B.principalBLMDatum ℓ).form = B.principalBLMForm ℓ := by
  simp [principalBLMDatum]

/-- The adapted basis `(a_j, c_i)` of the extension, with unfrozen indices the `a_i`,
`i ∈ I_uf`, and multipliers `principalBLMMultiplier`. -/
def principalBLMBasis : (B.principalBLMDatum ℓ).AdaptedBasis (ι ⊕ B.unfrozenIndex) :=
  AdaptedBasis.ofBasis _ _ _ _ _ _ _ _

@[simp]
theorem principalBLMBasis_basis :
    (B.principalBLMBasis ℓ).basis = Finsupp.basisSingleOne := by
  simp [principalBLMBasis]

@[simp]
theorem principalBLMBasis_unfrozenIndex :
    (B.principalBLMBasis ℓ).unfrozenIndex = B.unfrozenIndex.map .inl := by
  simp [principalBLMBasis]

@[simp]
theorem principalBLMBasis_multiplier :
    (B.principalBLMBasis ℓ).multiplier = B.principalBLMMultiplier ℓ := by
  simp [principalBLMBasis]

/-- The unfrozen indices of the extension are those of the original adapted basis. -/
def principalBLMUnfrozenEquiv : B.unfrozenIndex ≃ (B.principalBLMBasis ℓ).unfrozenIndex where
  toFun i := ⟨.inl i, by simp⟩
  invFun
    | ⟨.inl j, h⟩ => ⟨j, by simpa using h⟩
    | ⟨.inr _, h⟩ => absurd h (by simp)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨_ | _, h⟩
    · rfl
    · simp at h

@[simp]
theorem coe_principalBLMUnfrozenEquiv (i : B.unfrozenIndex) :
    (B.principalBLMUnfrozenEquiv ℓ i : ι ⊕ B.unfrozenIndex) = .inl i :=
  (rfl)

/-- The principal BLM extension: a polynomial input in the sense of Burcroff–Lee–Mou on the
extension `N^B`, with the unfrozen indices and multiplicities `ℓ_i` of the original adapted
basis and exponents `w_i = r(e_i)` (`principalBLMSpaceEquiv_principalBLMExponent`). -/
def principalBLMExtension [Nonempty ι] : (B.principalBLMBasis ℓ).BLMPolynomialInput where
  multiplicity i := ℓ ((B.principalBLMUnfrozenEquiv ℓ).symm i)
  multiplicity_pos _ := PNat.pos _
  exponent i := B.principalBLMExponent ((B.principalBLMUnfrozenEquiv ℓ).symm i)
  multiplicity_mul_exponent i a := by
    obtain ⟨i, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective i
    simp only [Equiv.symm_apply_apply, principalBLMBasis_basis, Finsupp.coe_basisSingleOne,
      coe_principalBLMUnfrozenEquiv, principalBLMDatum_form, principalBLMForm_single_inl,
      principalBLMBasis_multiplier, ← premultiplier_div_mul_multiplier B ℓ i,
      ← cast_principalBLMMultiplier_mul_principalBLMScale]
    ring
  isPrimitive_exponent i := TauCeti.isPrimitive_def.mpr
    ⟨Module.Dual.eval ℤ _ (Finsupp.single (.inr ((B.principalBLMUnfrozenEquiv ℓ).symm i)) 1),
      by simp [principalBLMExponent_apply]⟩
  eq_one_of_dvd_multiplier k hk := by
    have j := Classical.arbitrary ι
    refine Nat.dvd_one.mp ?_
    rw [← Finset.gcd_div_eq_one (Finset.mem_univ (.inl j)) (premultiplier_pos B ℓ _).ne']
    exact Finset.dvd_gcd fun b _ => by simpa [principalBLMMultiplier] using hk b
  eq_zero_of_form_eq_zero v hv h := by
    have hS := ((B.principalBLMBasis ℓ).mem_unfrozen_iff).mp hv.1
    simp only [principalBLMBasis_unfrozenIndex, principalBLMBasis_basis,
      Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply] at hS
    ext (j | i)
    · by_cases hj : j ∈ B.unfrozenIndex
      · have h' := h (Finsupp.single (.inr ⟨j, hj⟩) 1)
        rw [principalBLMDatum_form, principalBLMForm_single_inr, neg_eq_zero] at h'
        have hc := (B.principalBLMScale_pos ℓ).ne'
        have hd : (B.multiplier j : ℚ) ≠ 0 := by exact_mod_cast (B.multiplier_pos j).ne'
        simpa [hc, hd] using h'
      · exact hS _ (by simpa using hj)
    · exact hS _ (by simp)

@[simp]
theorem principalBLMExtension_multiplicity [Nonempty ι] (i : B.unfrozenIndex) :
    (B.principalBLMExtension ℓ).multiplicity (B.principalBLMUnfrozenEquiv ℓ i) = ℓ i :=
  (rfl)

@[simp]
theorem principalBLMExtension_exponent [Nonempty ι] (i : B.unfrozenIndex) :
    (B.principalBLMExtension ℓ).exponent (B.principalBLMUnfrozenEquiv ℓ i) =
      B.principalBLMExponent i :=
  (rfl)

end Form

end Mei.SkewLatticeDatum.AdaptedBasis
