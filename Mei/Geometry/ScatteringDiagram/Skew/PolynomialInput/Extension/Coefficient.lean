/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Coefficient

/-!
# Returning the BLM extension to principal coefficients

The space lattice of the BLM extension is the original principal lattice.
Restrict its spatial exponents to the principal coefficient monoid and retain
nonnegative independent-letter counts. Specializing each letter weight to its
independent polynomial variable gives a filtered algebra map to the original
principal realization. An initial term of multiplicity `s` becomes
`aᵢₛ q^(s eᵢ)`, including for degenerate and zero skew forms.

The principal degree lies between the alphabet degree and its product with
the largest letter multiplicity. Thus the substitution extends to the native
coefficient completions with identity cutoff modulus.

We use `principalBLMSpaceEquiv`, `PositiveDegrees.finiteAlphabetLift`,
`BLMPolynomialInput.coefficientWeight`, Mathlib's `AddMonoidAlgebra.lift`,
`LogarithmicVectorField.filtration_ideal_le_comap_coefficientDegreeMap`, and
`AlgFiltration.mapCompletionₐ`. The extension and specialization follow
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, §9.2
(arXiv:2503.03719v1), with the principal realization conventions of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis

open Module _root_.AddMonoidAlgebra

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N}
  (B : D.AdaptedBasis ι) [DecidableEq ι] [Fintype ι] [Nonempty ι]
  (ℓ : B.unfrozenIndex → ℕ+)

local notation "E" => BLMPolynomialInput.Letter (B.principalBLMExtension ℓ)
local notation "m" => BLMPolynomialInput.letterExponent (B.principalBLMExtension ℓ)
local notation "Γ" => Module.Dual ℤ ((ι ⊕ B.unfrozenIndex) →₀ ℤ) ×
  (E → ℤ)
local notation "L" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "d" => PositiveDegrees.finiteAlphabet m
local notation "e" => D.principalPositiveDegrees B.unfrozenBasis.positiveDegrees
local notation "Q" => D.principalCoefficientMonoid B.unfrozenBasis.positiveDegrees

/-- Forget the independent-letter counts and identify the extension's space
lattice with the original principal lattice. -/
def principalBLMExtensionLift : Γ →+ L :=
  B.principalBLMSpaceEquiv.toAddMonoidHom.comp (AddMonoidHom.fst _ _)

@[simp]
theorem principalBLMExtensionLift_apply (q : Γ) :
    B.principalBLMExtensionLift ℓ q = B.principalBLMSpaceEquiv q.1 := (rfl)

/-- Every initial alphabet letter becomes the corresponding positive multiple
of an original principal basis degree. -/
@[simp↓]
theorem principalBLMExtensionLift_letter (α : E) :
    B.principalBLMExtensionLift ℓ (PositiveDegrees.letter m α) =
      ((α.2 : ℕ) + 1) • D.principalEmbedding
        (B.unfrozenBasis ((B.principalBLMUnfrozenEquiv ℓ).symm α.1)) := by
  rcases α with ⟨j, s⟩
  obtain ⟨i, rfl⟩ := (B.principalBLMUnfrozenEquiv ℓ).surjective j
  simp only [principalBLMExtensionLift_apply, PositiveDegrees.letter_fst,
    BLMPolynomialInput.letterExponent_mk, map_nsmul, principalBLMExtension_exponent,
    principalBLMSpaceEquiv_principalBLMExponent, Equiv.symm_apply_apply]
  congr 2
  exact Subtype.ext (B.coe_unfrozenBasis i).symm

private theorem principalBLMExtensionLift_letter_mem (α : E) :
    B.principalBLMExtensionLift ℓ (PositiveDegrees.letter m α) ∈
      (e).monoid := by
  rw [principalBLMExtensionLift_letter, ← map_nsmul, principalEmbedding_apply,
    PositiveDegrees.mem_graph_monoid]
  refine ⟨nsmul_mem ?_ _, rfl⟩
  simp [Basis.mem_positiveDegrees_monoid, Finsupp.single_apply, ite_nonneg]

/-- A letter in slot `s` has principal degree `s+1`. -/
@[simp↓]
theorem degree_principalBLMExtensionLift_letter (α : E) :
    (e).degree (B.principalBLMExtensionLift ℓ
      (PositiveDegrees.letter m α)) = (α.2 : ℕ) + 1 := by
  rw [principalBLMExtensionLift_letter, map_nsmul]
  rw [principalEmbedding_apply, PositiveDegrees.graph_degree,
    Basis.positiveDegrees_degree, Basis.repr_self]
  simp only [Finsupp.single_apply, Fintype.sum_ite_eq, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]

/-- The extension alphabet maps to the original principal positive degrees
with identity cutoff modulus. -/
def principalBLMExtensionDegreeMap : PositiveDegreeMap d e :=
  PositiveDegrees.finiteAlphabetLift m
    (B.principalBLMExtensionLift_letter_mem ℓ)
    (fun α h => by
      have := B.degree_principalBLMExtensionLift_letter ℓ α
      rw [h, map_zero] at this
      omega)

@[simp]
theorem principalBLMExtensionDegreeMap_apply (q : Γ) :
    B.principalBLMExtensionDegreeMap ℓ q = B.principalBLMExtensionLift ℓ q :=
  PositiveDegrees.finiteAlphabetLift_apply _ _ _ q

@[simp]
theorem principalBLMExtensionDegreeMap_modulus (k : ℕ) :
    (B.principalBLMExtensionDegreeMap ℓ).modulus k = k :=
  PositiveDegrees.finiteAlphabetLift_modulus _ _ _ k

/-- Principal order lies between alphabet order and the alphabet order times
any uniform bound on the input multiplicities. -/
theorem degree_principalBLMExtensionLift_bounds (c : ℕ)
    (hc : ∀ i, (ℓ i : ℕ) ≤ c) {q : Γ} (hq : q ∈ (d).monoid) :
    (d).degree q ≤ (e).degree (B.principalBLMExtensionLift ℓ q) ∧
      (e).degree (B.principalBLMExtensionLift ℓ q) ≤ c * (d).degree q := by
  refine ⟨PositiveDegrees.finiteAlphabet_degree_le _
    (B.principalBLMExtensionLift_letter_mem ℓ)
    (fun α => by
      simpa only [principalBLMExtensionDegreeMap_apply] using
        (B.principalBLMExtensionDegreeMap ℓ).map_ne_zero
          (PositiveDegrees.letter_mem _ α) (PositiveDegrees.letter_ne_zero _ α)) hq, ?_⟩
  refine PositiveDegrees.finiteAlphabet_degree_map_le_mul m
    (τ := B.principalBLMExtensionLift ℓ) (fun α => ?_) hq
  rw [degree_principalBLMExtensionLift_letter]
  have hα := α.2.isLt
  have hm : (B.principalBLMExtension ℓ).multiplicity α.1 =
      ℓ ((B.principalBLMUnfrozenEquiv ℓ).symm α.1) := by
    simpa only [Equiv.apply_symm_apply] using B.principalBLMExtension_multiplicity ℓ
      ((B.principalBLMUnfrozenEquiv ℓ).symm α.1)
  have hb := hc ((B.principalBLMUnfrozenEquiv ℓ).symm α.1)
  have hs : (α.2 : ℕ) + 1 ≤ c := by omega
  exact_mod_cast hs

/-- Coefficient exponents have arbitrary original Laurent character,
nonnegative original principal coordinates, and nonnegative letter counts. -/
def principalBLMExtensionCoefficientMonoid : AddSubmonoid Γ :=
  ((Q).comap B.principalBLMSpaceEquiv.toAddMonoidHom).prod
    (PositiveDegrees.orthant E).monoid

@[simp]
theorem mem_principalBLMExtensionCoefficientMonoid (q : Γ) :
    q ∈ B.principalBLMExtensionCoefficientMonoid ℓ ↔
      (B.principalBLMSpaceEquiv q.1).2 ∈ B.unfrozenBasis.positiveDegrees.monoid ∧
        ∀ α, 0 ≤ q.2 α := by
  simp [principalBLMExtensionCoefficientMonoid, AddSubmonoid.mem_prod]

/-- The extension coefficient monoid is a submonoid of the BLM Laurent
coefficient monoid, so its existing polynomial weights restrict. -/
theorem principalBLMExtensionCoefficientMonoid_le :
    B.principalBLMExtensionCoefficientMonoid ℓ ≤ (B.principalBLMExtension ℓ).coefficientMonoid :=
  fun q hq => ((B.principalBLMExtension ℓ).mem_coefficientMonoid q).mpr
    ((B.mem_principalBLMExtensionCoefficientMonoid ℓ q).mp hq).2

/-- Every positive alphabet increment is an allowed coefficient exponent. -/
theorem positiveDegrees_le_principalBLMExtensionCoefficientMonoid :
    (d).monoid ≤ B.principalBLMExtensionCoefficientMonoid ℓ := by
  intro q hq
  refine (B.mem_principalBLMExtensionCoefficientMonoid ℓ q).mpr ⟨?_,
    ((PositiveDegrees.mem_finiteAlphabet_monoid _).mp hq).1⟩
  exact (D.mem_principalCoefficientMonoid _ _).mp
    (D.principalPositiveDegrees_le_coefficientMonoid _
      (by simpa using (B.principalBLMExtensionDegreeMap ℓ).map_mem hq))

local notation "P" => B.principalBLMExtensionCoefficientMonoid ℓ

/-- An initial alphabet letter in the restricted extension coefficient monoid. -/
def principalBLMExtensionCoefficientLetter (α : E) : P :=
  ⟨PositiveDegrees.letter m α,
    B.positiveDegrees_le_principalBLMExtensionCoefficientMonoid ℓ
      (PositiveDegrees.letter_mem _ α)⟩

@[simp]
theorem coe_principalBLMExtensionCoefficientLetter
    (α : E) :
    (B.principalBLMExtensionCoefficientLetter ℓ α).val =
      PositiveDegrees.letter m α := (rfl)

/-- Inclusion recovers the same letter of the original BLM coefficient monoid. -/
@[simp]
theorem inclusion_principalBLMExtensionCoefficientLetter
    (α : E) :
    AddSubmonoid.inclusion (B.principalBLMExtensionCoefficientMonoid_le ℓ)
        (B.principalBLMExtensionCoefficientLetter ℓ α) =
      (B.principalBLMExtension ℓ).coefficientLetter α := by
  apply Subtype.ext
  simp

/-- The specialization on coefficient exponents. -/
def principalBLMExtensionCoefficientExponent : P →+ Q :=
  ((B.principalBLMExtensionLift ℓ).comp (P).subtype).codRestrict Q (fun q =>
    (D.mem_principalCoefficientMonoid _ _).mpr
      ((B.mem_principalBLMExtensionCoefficientMonoid ℓ q.val).mp q.property).1)

@[simp]
theorem coe_principalBLMExtensionCoefficientExponent (q : P) :
    (B.principalBLMExtensionCoefficientExponent ℓ q).val =
      B.principalBLMSpaceEquiv q.val.1 := (rfl)

/-- The image of a coefficient letter is `s r(eᵢ)` in the original principal lattice. -/
@[simp↓]
theorem coe_principalBLMExtensionCoefficientExponent_letter
    (α : E) :
    (B.principalBLMExtensionCoefficientExponent ℓ
        (B.principalBLMExtensionCoefficientLetter ℓ α)).val =
      ((α.2 : ℕ) + 1) • D.principalEmbedding
        (B.unfrozenBasis ((B.principalBLMUnfrozenEquiv ℓ).symm α.1)) := by
  simpa only [principalBLMExtensionLift_apply,
    coe_principalBLMExtensionCoefficientExponent,
    coe_principalBLMExtensionCoefficientLetter, PositiveDegrees.letter_fst] using
    B.principalBLMExtensionLift_letter ℓ α

private theorem map_principalBLMExtensionCoefficientMonoid_le :
    (P).map (B.principalBLMExtensionDegreeMap ℓ).toAddMonoidHom ≤ Q := by
  rintro _ ⟨q, hq, rfl⟩
  simpa only [coe_principalBLMExtensionCoefficientExponent,
    principalBLMExtensionDegreeMap_apply, principalBLMExtensionLift_apply] using
    (B.principalBLMExtensionCoefficientExponent ℓ ⟨q, hq⟩).property

section Semiring

variable (R : Type*) [CommSemiring R]

private def extensionWeight : Multiplicative P →* MvPolynomial E R :=
  ((B.principalBLMExtension ℓ).coefficientWeight R).comp
    (AddSubmonoid.inclusion (B.principalBLMExtensionCoefficientMonoid_le ℓ)).toMultiplicative

private def extensionTwist : R[P] →ₐ[R] (MvPolynomial E R)[P] :=
  lift R _ _ (singleHom.comp ((B.extensionWeight ℓ R).prod (MonoidHom.id _)))

private theorem extensionTwist_single (q : P) (r : R) :
    B.extensionTwist ℓ R (single q r) =
      single q (MvPolynomial.C r * B.extensionWeight ℓ R (.ofAdd q)) := by
  simp [extensionTwist, lift_single, Algebra.smul_def, singleHom, single_mul_single]

/-- Substitute the independent variables into the original principal
coefficient algebra; the polynomial weights need not be units. -/
def principalBLMExtensionCoefficientMap : R[P] →ₐ[R] (MvPolynomial E R)[Q] :=
  (AlgHom.restrictScalars R (mapDomainAlgHom (MvPolynomial E R) (MvPolynomial E R)
    ((AddSubmonoid.inclusion (B.map_principalBLMExtensionCoefficientMonoid_le ℓ)).comp
      ((B.principalBLMExtensionDegreeMap ℓ).toAddMonoidHom.addSubmonoidMap P)))).comp
    (B.extensionTwist ℓ R)

/-- Each monomial keeps its full polynomial weight before exponents merge. -/
@[simp]
theorem principalBLMExtensionCoefficientMap_single (q : P) (r : R) :
    B.principalBLMExtensionCoefficientMap ℓ R (single q r) =
      single (B.principalBLMExtensionCoefficientExponent ℓ q)
        (MvPolynomial.C r * MvPolynomial.monomial
          ((B.principalBLMExtension ℓ).coefficientMultiplicity
            (AddSubmonoid.inclusion (B.principalBLMExtensionCoefficientMonoid_le ℓ) q)) 1) := by
  simp only [principalBLMExtensionCoefficientMap, AlgHom.comp_apply, extensionTwist_single,
    AlgHom.restrictScalars_apply, mapDomainAlgHom_apply, mapDomain_single,
    extensionWeight, MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
    BLMPolynomialInput.coefficientWeight_apply]
  congr 1
  apply Subtype.ext
  simp [coe_principalBLMExtensionCoefficientExponent, principalBLMExtensionDegreeMap_apply,
    principalBLMExtensionLift_apply]

/-- The initial BLM polynomial in the restricted coefficient monoid. -/
def principalBLMExtensionInitialFunction
    (i : (B.principalBLMBasis ℓ).unfrozenIndex) : R[P] :=
  1 + ∑ s : Fin ((B.principalBLMExtension ℓ).multiplicity i),
    single (B.principalBLMExtensionCoefficientLetter ℓ ⟨i, s⟩) 1

/-- The restricted initial function is the finite sum of its coefficient letters. -/
theorem principalBLMExtensionInitialFunction_def
    (i : (B.principalBLMBasis ℓ).unfrozenIndex) :
    B.principalBLMExtensionInitialFunction ℓ R i =
      1 + ∑ s : Fin ((B.principalBLMExtension ℓ).multiplicity i),
        single (B.principalBLMExtensionCoefficientLetter ℓ ⟨i, s⟩) 1 := (rfl)

/-- Inclusion recovers the actual initial BLM coefficient polynomial. -/
@[simp↓]
theorem mapDomain_principalBLMExtensionInitialFunction
    (i : (B.principalBLMBasis ℓ).unfrozenIndex) :
    mapDomainAlgHom R R (AddSubmonoid.inclusion
        (B.principalBLMExtensionCoefficientMonoid_le ℓ))
        (B.principalBLMExtensionInitialFunction ℓ R i) =
      (B.principalBLMExtension ℓ).initialCoefficientFunction R i := by
  rw [principalBLMExtensionInitialFunction_def, map_add, map_one, map_sum,
    BLMPolynomialInput.initialCoefficientFunction_def]
  simp [mapDomainAlgHom_apply, mapDomain_single]

/-- The initial functions become the original principal polynomials with
independent coefficients and the prescribed positive multiples of `r(eᵢ)`. -/
@[simp]
theorem principalBLMExtensionCoefficientMap_initialFunction
    (i : (B.principalBLMBasis ℓ).unfrozenIndex) :
    B.principalBLMExtensionCoefficientMap ℓ R
        (B.principalBLMExtensionInitialFunction ℓ R i) =
      1 + ∑ s : Fin ((B.principalBLMExtension ℓ).multiplicity i),
        single (B.principalBLMExtensionCoefficientExponent ℓ
          (B.principalBLMExtensionCoefficientLetter ℓ ⟨i, s⟩))
          (MvPolynomial.X ⟨i, s⟩) := by
  simp [principalBLMExtensionInitialFunction_def, MvPolynomial.X]

/-- The specialization preserves positive-increment ideals with identity
cutoff modulus. In particular the old principal variables are not inverted. -/
theorem filtration_ideal_le_comap_principalBLMExtensionCoefficientMap (k : ℕ) :
    (TropicalVertexCoefficientAction.filtration (R := R) d P).ideal (k + 1) ≤
      ((TropicalVertexCoefficientAction.filtration (R := MvPolynomial E R) e Q).ideal
        (k + 1)).comap (B.principalBLMExtensionCoefficientMap ℓ R) := by
  simpa only [principalBLMExtensionDegreeMap_modulus, principalBLMExtensionCoefficientMap] using
    LogarithmicVectorField.filtration_ideal_le_comap_coefficientDegreeMap
      d P (Algebra.ofId R (MvPolynomial E R))
      (B.extensionWeight ℓ R) (B.extensionTwist ℓ R) (B.extensionTwist_single ℓ R)
      (B.principalBLMExtensionDegreeMap ℓ) (B.map_principalBLMExtensionCoefficientMonoid_le ℓ) k

end Semiring

section Completion

variable {R : Type*} [CommRing R]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d P
local notation "G" => TropicalVertexCoefficientAction.filtration
  (R := MvPolynomial E R) e Q

/-- The extension substitution on completed principal coefficients, retaining
the identity cutoff modulus. -/
def principalBLMExtensionCompletionMap : (F).completion →ₐ[R] (G).completion :=
  (F).mapCompletionₐ G (B.principalBLMExtensionCoefficientMap ℓ R) id monotone_id
    (B.filtration_ideal_le_comap_principalBLMExtensionCoefficientMap ℓ R)

/-- Every finite projection is the same-order quotient substitution. -/
@[simp]
theorem projection_principalBLMExtensionCompletionMap (k : ℕ) (a : (F).completion) :
    (G).projection k (B.principalBLMExtensionCompletionMap ℓ a) =
      Ideal.quotientMapₐ ((G).ideal (k + 1)) (B.principalBLMExtensionCoefficientMap ℓ R)
        (B.filtration_ideal_le_comap_principalBLMExtensionCoefficientMap ℓ R k)
        ((F).projection k a) :=
  (F).projection_mapCompletionₐ G _ id monotone_id _ k a

/-- The completed map extends the finite polynomial substitution. -/
@[simp]
theorem principalBLMExtensionCompletionMap_toCompletion (a : R[P]) :
    B.principalBLMExtensionCompletionMap ℓ ((F).toCompletion a) =
      (G).toCompletion (B.principalBLMExtensionCoefficientMap ℓ R a) :=
  (F).mapCompletionₐ_toCompletion G _ id monotone_id _ a

end Completion

end Mei.SkewLatticeDatum.AdaptedBasis
