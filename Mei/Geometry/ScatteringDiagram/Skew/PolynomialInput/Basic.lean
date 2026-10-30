/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.AdaptedBasis
public import Mei.Algebra.PositiveDegrees.FiniteAlphabet
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Polynomial inputs of generalized cluster scattering diagrams

Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §8.1
(arXiv:2503.03719v1, Definitions 8.1 and 8.2 and the injectivity assumption (8.3)), attach
a scattering diagram in `M_ℝ`, `M = Hom(N, ℤ)`, to the following data: a skew lattice datum
`(N, N_uf, N°, {,})`, an adapted basis `(e_i)` with multipliers `d_i` of greatest common
divisor one, and positive integers `ℓ_i` at the unfrozen indices such that, for the form
`ω = -{,}`, every vector
`w_i = ω(-, d_i e_i) / ℓ_i = d_i {e_i, -} / ℓ_i`
is a primitive element of `M`, and `N_uf ∩ N° → M`, `v ↦ ω(-, v)`, is injective. With
independent monoid variables `p_{i,s}`, `1 ≤ s ≤ ℓ_i`, the initial wall at an unfrozen `i`
has support `e_i⊥` and function `f_i = 1 + ∑_s p_{i,s} z^{s w_i}`.

We record these conditions as `SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput`. The
exponent `w_i` is part of the data, determined by `ℓ_i w_i = d_i {e_i, -}`; equivalently
`ℓ_i w_i = -{-, κ(e_i) e_i}` is the negated integral normal of `e_i`. Each `w_i` vanishes on
`e_i`, so the exponents `s w_i` are tangent to the wall `e_i⊥`.

The variables `p_{i,s}` are the letters of a finite alphabet (`Mei.PositiveDegrees.finiteAlphabet`)
over the exponents `m_{i,s} = s w_i`: identifying `p_{i,s} z^{s w_i}` with the monomial of the
letter `v_{i,s} = (s w_i, e_{(i,s)})` of `M × ℤ^E` presents the initial functions
(`BLMPolynomialInput.initialFunction`) in the monoid algebra of the alphabet lattice, where
distinct variables span distinct supported rays even when their exponents are proportional.
The coefficient monoid `BLMPolynomialInput.coefficientMonoid` also allows arbitrary Laurent
characters, with nonnegative multiplicities of the independent variables; the native initial
functions `BLMPolynomialInput.initialCoefficientFunction` map to `initialFunction` under inclusion.

A basis vector `e_i` with `i ∈ I_uf` cannot lie in the radical of the form, so the zero form
admits no such input when `I_uf` is nonempty (`BLMPolynomialInput.isEmpty_of_form_eq_zero`).
On the rank-two datum with `{e₁, e₂} = 1` and `d = (1, 2)`, the multiplicities `ℓ = (1, 2)` give
an input with exponents `w₁ = e₂*` and `w₂ = -e₁*`, whereas `ℓ₂ = 1` would give the imprimitive
vector `-2 e₁*` (`Mei.SkewLatticeDatum.Examples.rankTwoBLMPolynomialInput`, in
`Mei.Geometry.ScatteringDiagram.Skew.Examples`).

## Main declarations

* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput`: the lattice data of a polynomial
  input of a generalized cluster scattering diagram.
* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.cast_exponent_apply`:
  `w_i(a) = d_i {e_i, a} / ℓ_i`.
* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.multiplicity_smul_exponent`:
  `ℓ_i w_i = -{-, κ(e_i) e_i}`.
* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.exponent_apply_basis_self`: `w_i(e_i) = 0`.
* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.initialFunction`: the initial wall
  functions `1 + ∑_s p_{i,s} z^{s w_i}`.
* `Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.isEmpty_of_form_eq_zero`: the zero form
  has no polynomial input with a nonempty unfrozen part.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

variable {N : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {ι : Type*}

/-- The lattice data of a polynomial input of a generalized cluster scattering diagram on an
adapted basis `(e_i)` with multipliers `d_i` (Burcroff–Lee–Mou, Definitions 8.1 and 8.2):
positive multiplicities `ℓ_i` at the unfrozen indices, the multipliers having greatest common
divisor one, such that each `w_i` with `ℓ_i w_i = ω(-, d_i e_i) = d_i {e_i, -}` is a primitive
integral functional on `N`, together with the injectivity of `N_uf ∩ N° → Hom(N, ℤ)`,
`v ↦ ω(-, v)`. Here `ω = -{,}`. The multiplicities at frozen indices are `1` by convention and
are not recorded. -/
structure BLMPolynomialInput (B : D.AdaptedBasis ι) where
  /-- The multiplicity `ℓ_i` of an unfrozen index: the number of variables `p_{i,s}`. -/
  multiplicity : B.unfrozenIndex → ℕ
  /-- The multiplicities are positive. -/
  multiplicity_pos : ∀ i, 0 < multiplicity i
  /-- The exponent `w_i ∈ M = Hom(N, ℤ)` of the initial wall at an unfrozen index. -/
  exponent : B.unfrozenIndex → Module.Dual ℤ N
  /-- The exponent is `ω(-, d_i e_i) / ℓ_i`: `ℓ_i w_i(a) = d_i {e_i, a}`. -/
  multiplicity_mul_exponent : ∀ i a,
    (multiplicity i : ℚ) * exponent i a = B.multiplier i * D.form (B.basis i) a
  /-- Each exponent `w_i` is primitive in `M`. -/
  isPrimitive_exponent : ∀ i, TauCeti.IsPrimitive (exponent i)
  /-- The multipliers `d_i` have greatest common divisor one. -/
  eq_one_of_dvd_multiplier : ∀ k : ℕ, (∀ i, k ∣ B.multiplier i) → k = 1
  /-- The injectivity assumption: a vector of `N_uf ∩ N°` with `ω(-, v) = 0` vanishes. -/
  eq_zero_of_form_eq_zero : ∀ v ∈ D.unfrozen ⊓ D.sublattice, (∀ a, D.form a v = 0) → v = 0

namespace BLMPolynomialInput

variable {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)

/-- The value `w_i(a) = d_i {e_i, a} / ℓ_i` of an exponent. -/
theorem cast_exponent_apply (i : B.unfrozenIndex) (a : N) :
    (I.exponent i a : ℚ) = B.multiplier i * D.form (B.basis i) a / I.multiplicity i := by
  have hℓ : (I.multiplicity i : ℚ) ≠ 0 := by exact_mod_cast (I.multiplicity_pos i).ne'
  rw [← I.multiplicity_mul_exponent, mul_div_cancel_left₀ _ hℓ]

/-- A polynomial input is determined by its multiplicities. -/
@[ext]
theorem ext {I J : B.BLMPolynomialInput} (h : I.multiplicity = J.multiplicity) : I = J := by
  have hw : I.exponent = J.exponent := by
    funext i
    ext a
    apply Int.cast_injective (α := ℚ)
    rw [I.cast_exponent_apply, J.cast_exponent_apply, h]
  cases I
  cases J
  cases h
  cases hw
  rfl

/-- The exponent `w_i` vanishes on `e_i`: the exponents of the initial wall at `i` are tangent
to its support `e_i⊥`. -/
@[simp]
theorem exponent_apply_basis_self (i : B.unfrozenIndex) : I.exponent i (B.basis i) = 0 := by
  apply Int.cast_injective (α := ℚ)
  simp [I.cast_exponent_apply]

/-- The exponents are nonzero. -/
@[simp]
theorem exponent_ne_zero (i : B.unfrozenIndex) : I.exponent i ≠ 0 :=
  (I.isPrimitive_exponent i).ne_zero

/-- The multiple `ℓ_i w_i` is the negated integral normal `-{-, κ(e_i) e_i}` of `e_i`. -/
theorem multiplicity_smul_exponent [Module.Free ℤ N] (i : B.unfrozenIndex) :
    I.multiplicity i • I.exponent i = -D.normal (B.basis i) (B.basis_mem_unfrozen i) := by
  ext a
  apply Int.cast_injective (α := ℚ)
  rw [LinearMap.smul_apply, LinearMap.neg_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    I.multiplicity_mul_exponent, Int.cast_neg, D.cast_normal_apply, B.rayIndex_basis,
    D.form_swap]
  ring

include I in
/-- An unfrozen basis vector `e_i` does not lie in the radical of the form. -/
theorem exists_form_basis_ne_zero (i : B.unfrozenIndex) : ∃ a, D.form (B.basis i) a ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, I.exponent i a ≠ 0 := by
    by_contra! h
    exact I.exponent_ne_zero i (LinearMap.ext h)
  refine ⟨a, fun h => ha (Int.cast_injective (α := ℚ) ?_)⟩
  rw [I.cast_exponent_apply, h]
  simp

/-- The zero form admits no polynomial input with a nonempty unfrozen part. For `N_uf ≠ 0` the
map `v ↦ ω(-, v)` on `N_uf ∩ N°` vanishes and is not injective. -/
theorem isEmpty_of_form_eq_zero (hform : D.form = 0) (hI : B.unfrozenIndex.Nonempty) :
    IsEmpty B.BLMPolynomialInput := by
  refine ⟨fun I => ?_⟩
  obtain ⟨i, hi⟩ := hI
  obtain ⟨a, ha⟩ := I.exists_form_basis_ne_zero ⟨i, hi⟩
  simp [hform] at ha

section Letter

/-- The variables `p_{i,s}` of a polynomial input, indexed by an unfrozen `i` and
`s - 1 ∈ Fin ℓ_i`. -/
abbrev Letter := Σ i : B.unfrozenIndex, Fin (I.multiplicity i)

/-- The exponent `s w_i ∈ M` carried by the variable `p_{i,s}` in the initial function at `i`. -/
def letterExponent (α : I.Letter) : Module.Dual ℤ N :=
  ((α.2 : ℕ) + 1) • I.exponent α.1

@[simp]
theorem letterExponent_mk (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) :
    I.letterExponent ⟨i, s⟩ = ((s : ℕ) + 1) • I.exponent i :=
  (rfl)

/-- The exponents of the initial function at `i` vanish on `e_i`: they are tangent to the
wall `e_i⊥`. -/
theorem letterExponent_apply_basis_self (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) :
    I.letterExponent ⟨i, s⟩ (B.basis i) = 0 := by
  simp

variable [DecidableEq ι]

/-- The initial wall function `f_i = 1 + ∑_{s=1}^{ℓ_i} p_{i,s} z^{s w_i}` at an unfrozen index,
in the monoid algebra of the finite alphabet lattice `M × ℤ^E`, where the monomial of the
letter `v_{i,s} = (s w_i, e_{(i,s)})` represents `p_{i,s} z^{s w_i}`. -/
def initialFunction (R : Type*) [Semiring R] (i : B.unfrozenIndex) :
    AddMonoidAlgebra R (Module.Dual ℤ N × (I.Letter → ℤ)) :=
  1 + ∑ s : Fin (I.multiplicity i),
    AddMonoidAlgebra.single (PositiveDegrees.letter I.letterExponent ⟨i, s⟩) 1

/-- The initial wall function is the finite sum of the constant term and its variable monomials. -/
theorem initialFunction_def (R : Type*) [Semiring R] (i : B.unfrozenIndex) :
    I.initialFunction R i = 1 + ∑ s : Fin (I.multiplicity i),
      AddMonoidAlgebra.single (PositiveDegrees.letter I.letterExponent ⟨i, s⟩) 1 :=
  (rfl)

/-- The coefficient of the initial function at `i` on the letter of a variable `p_{j,s}`
is `1` if `j = i` and `0` otherwise. -/
@[simp]
theorem coeff_initialFunction_letter (R : Type*) [Semiring R] (i : B.unfrozenIndex)
    (α : I.Letter) :
    (I.initialFunction R i).coeff (PositiveDegrees.letter I.letterExponent α) =
      if α.1 = i then 1 else 0 := by
  have hinj := (PositiveDegrees.linearIndependent_letter I.letterExponent).injective
  simp only [initialFunction, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.single_eq_of_ne (PositiveDegrees.letter_ne_zero _ α), zero_add]
  obtain ⟨j, s⟩ := α
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl, Finset.sum_eq_single s, Finsupp.single_eq_same]
    · exact fun c _ hc => Finsupp.single_eq_of_ne fun h =>
        hc (eq_of_heq (Sigma.mk.inj (hinj h)).2).symm
    · simp
  · simp only [hji, ↓reduceIte]
    exact Finset.sum_eq_zero fun c _ => Finsupp.single_eq_of_ne fun h =>
      hji (congrArg Sigma.fst (hinj h))

/-- The constant coefficient of an initial function is `1`. -/
@[simp]
theorem coeff_initialFunction_zero (R : Type*) [Semiring R] (i : B.unfrozenIndex) :
    (I.initialFunction R i).coeff 0 = 1 := by
  simp [initialFunction, AddMonoidAlgebra.one_def, (PositiveDegrees.letter_ne_zero _ _).symm]

/-- Away from `0` and the letters of the variables `p_{i,s}`, the initial function at `i` has
zero coefficient. -/
@[simp]
theorem coeff_initialFunction_eq_zero (R : Type*) [Semiring R] (i : B.unfrozenIndex)
    {x : Module.Dual ℤ N × (I.Letter → ℤ)} (h0 : x ≠ 0)
    (hx : ∀ s, x ≠ PositiveDegrees.letter I.letterExponent ⟨i, s⟩) :
    (I.initialFunction R i).coeff x = 0 := by
  simp [initialFunction, AddMonoidAlgebra.one_def, h0.symm, fun s => (hx s).symm]

end Letter

section Coefficient

open _root_.AddMonoidAlgebra

variable [DecidableEq ι] [Fintype ι]

local notation "d" => PositiveDegrees.finiteAlphabet I.letterExponent

/-- The BLM coefficient exponents: arbitrary Laurent character and nonnegative
multiplicities of the independent variables. -/
def coefficientMonoid : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)) :=
  (⊤ : AddSubmonoid (Module.Dual ℤ N)).prod (PositiveDegrees.orthant I.Letter).monoid

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem mem_coefficientMonoid (q : Module.Dual ℤ N × (I.Letter → ℤ)) :
    q ∈ I.coefficientMonoid ↔ ∀ α, 0 ≤ q.2 α := by
  simp [coefficientMonoid, AddSubmonoid.mem_prod]

omit [DecidableEq ι] [Fintype ι] in
/-- The alphabet's positive degrees are allowed coefficient exponents. -/
theorem positiveDegrees_le_coefficientMonoid : (d).monoid ≤ I.coefficientMonoid :=
  fun _ h => (I.mem_coefficientMonoid _).mpr
    ((PositiveDegrees.mem_finiteAlphabet_monoid _).mp h).1

/-- The multiplicities of a coefficient exponent, as a polynomial multi-index.
The Laurent character does not contribute to this index. -/
def coefficientMultiplicity : I.coefficientMonoid →+ (I.Letter →₀ ℕ) where
  toFun q := Finsupp.equivFunOnFinite.symm (fun α => (q.val.2 α).toNat)
  map_zero' := by ext; simp
  map_add' q r := by
    ext α
    simp [Int.toNat_add ((I.mem_coefficientMonoid _).mp q.property α)
      ((I.mem_coefficientMonoid _).mp r.property α)]

omit [DecidableEq ι] in
@[simp]
theorem coefficientMultiplicity_apply (q : I.coefficientMonoid) (α : I.Letter) :
    I.coefficientMultiplicity q α = (q.val.2 α).toNat := (rfl)

/-- The coefficient exponent of the independent variable `p_{i,s} z^{s w_i}`. -/
def coefficientLetter (α : I.Letter) : I.coefficientMonoid :=
  ⟨PositiveDegrees.letter I.letterExponent α,
    I.positiveDegrees_le_coefficientMonoid (PositiveDegrees.letter_mem _ α)⟩

omit [Fintype ι] in
@[simp]
theorem coe_coefficientLetter (α : I.Letter) :
    (I.coefficientLetter α).val = PositiveDegrees.letter I.letterExponent α := (rfl)

@[simp]
theorem coefficientMultiplicity_coefficientLetter (α : I.Letter) :
    I.coefficientMultiplicity (I.coefficientLetter α) = Finsupp.single α 1 := by
  ext β
  simp [Finsupp.single_apply, Pi.single_apply, apply_ite Int.toNat, eq_comm]

variable (R : Type*) [Semiring R]

/-- The initial function in the coefficient monoid, retaining all independent variables. -/
def initialCoefficientFunction (i : B.unfrozenIndex) : R[I.coefficientMonoid] :=
  1 + ∑ s : Fin (I.multiplicity i), single (I.coefficientLetter ⟨i, s⟩) 1

omit [Fintype ι] in
/-- The native initial function is the constant term plus its independent-variable monomials. -/
theorem initialCoefficientFunction_def (i : B.unfrozenIndex) :
    I.initialCoefficientFunction R i = 1 + ∑ s : Fin (I.multiplicity i),
      single (I.coefficientLetter ⟨i, s⟩) 1 :=
  (rfl)

omit [Fintype ι] in
/-- Forgetting the coefficient-monoid restriction gives the original BLM initial function. -/
@[simp]
theorem mapDomain_initialCoefficientFunction (i : B.unfrozenIndex) :
    mapDomain Subtype.val (I.initialCoefficientFunction R i) = I.initialFunction R i := by
  have h : mapDomainRingHom R I.coefficientMonoid.subtype
      (I.initialCoefficientFunction R i) = I.initialFunction R i := by
    rw [initialCoefficientFunction_def, map_add, map_one, map_sum, initialFunction_def]
    simp [mapDomainRingHom_apply, mapDomain_single]
  simpa only [mapDomainRingHom_apply, AddSubmonoid.coe_subtype] using h

end Coefficient

end BLMPolynomialInput

end Mei.SkewLatticeDatum.AdaptedBasis
