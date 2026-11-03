/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Group.Hom.Int
public import Mei.Algebra.Lie.Logarithmic.Coefficient
public import Mei.Algebra.Lie.Logarithmic.Pairing.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Examples for the tropical vertex Lie algebra

Four small computations delimit the tropical vertex Lie algebra of formal logarithmic
derivations `z^n ∂_m` and its tropical pairings.

* In rank three the degree-`e₁` piece contains the independent fields
  `z^{e₁} ∂_{e₂*}` and `z^{e₁} ∂_{e₃*}`, and the bracket of `z^{e₁} ∂_{e₃*}` with
  `z^{e₂} ∂_{e₁*}` is `-z^{e₁+e₂} ∂_{e₃*}`, although `e₃*(e₂) = 0`: only the term
  `e₁*(e₁) = 1` survives.
* For the monoid `ℕ e₁ ⊆ ℤ²` the nonzero field `z^{e₁} ∂_{e₂*}` acts by zero on the
  coefficient algebra of the monoid, since every degree has vanishing second coordinate.
  The Lie algebra retains the character, so a field is not determined by its action on
  this coefficient algebra.
* The degree map `(a, b) ↦ a + b` from `ℕ²` to `ℕ` is a positive degree map, but it
  admits no tropical pairing on any character space containing `e₁*`: the degrees
  `(1, 0)` and `(0, 1)` have the same image and different `e₁*`-values. Correspondingly,
  there is no derivation of `ℚ[z]` intertwining `y x ∂_x` on `ℚ[x, y]` with the
  substitution `x, y ↦ z`, since `x - y ↦ 0` while `y x ∂_x (x - y) = x y ↦ z²`.
* For `T (a, b) = (2 a, b)` the character map `m ↦ m ∘ T⁻¹`, computed over `ℚ`, is a
  tropical pairing, and it sends `z^{e₂} ∂_{e₁*}` to `(1/2) z^{e₂} ∂_{e₁*}`.

The Lie algebra of logarithmic derivations and the pairing condition are those of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField.Examples

open _root_.AddMonoidAlgebra Polynomial

section Rank3

/-- The standard basis vector `e_i` of `ℤ³`. -/
local notation "e[" i "]" => (Pi.single i 1 : Fin 3 → ℤ)

local notation "ρ₃" => AddMonoidHom.id (Fin 3 → ℤ)

/-- The fields `z^{e₁} ∂_{e₂*}` and `z^{e₁} ∂_{e₃*}` are linearly independent. -/
theorem linearIndependent_single_coordinate :
    LinearIndependent ℚ ![single ρ₃ e[0] (coordinate 1), single ρ₃ e[0] (coordinate 2)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 : single ρ₃ e[0] (s • coordinate 1 + t • coordinate 2) = single ρ₃ e[0] 0 := by
    rw [map_add, map_smul, map_smul, h, map_zero]
  have h1 := single_injective ρ₃ e[0] h0
  have h2 := DFunLike.congr_fun h1 e[1]
  have h3 := DFunLike.congr_fun h1 e[2]
  exact ⟨by simpa using h2, by simpa using h3⟩

/-- Both fields lie in the degree-`e₁` piece of the tropical vertex Lie algebra. -/
theorem single_coordinate_mem_tropicalVertexLieAlgebra (i : Fin 3) (hi : i ≠ 0) :
    single ρ₃ e[0] (coordinate i) ∈
      tropicalVertexLieAlgebra (R := ℚ) (PositiveDegrees.orthant (Fin 3)) ρ₃ :=
  single_mem_tropicalVertexLieAlgebra _ _ (PositiveDegrees.single_mem_orthant_monoid 0) (by simp) _
    (by simp [hi])

/-- The bracket of `z^{e₁} ∂_{e₃*}` with `z^{e₂} ∂_{e₁*}` is `-z^{e₁+e₂} ∂_{e₃*}`, even though
`e₃*(e₂) = 0`. -/
theorem bracket_single_coordinate :
    ⁅single ρ₃ e[0] (coordinate 2), single ρ₃ e[1] (coordinate 0)⁆ =
      -single ρ₃ (e[0] + e[1]) (coordinate 2) := by
  rw [single_bracket_single, ← map_neg]
  congr 1
  simp

/-- The bracket of `z^{e₁} ∂_{e₃*}` with `z^{e₂} ∂_{e₁*}` is nonzero. -/
theorem bracket_single_coordinate_ne_zero :
    ⁅single ρ₃ e[0] (coordinate 2), single ρ₃ e[1] (coordinate 0)⁆ ≠ 0 := by
  rw [bracket_single_coordinate, neg_ne_zero]
  intro h
  have h1 := single_injective ρ₃ _ (h.trans (map_zero _).symm)
  have h2 := DFunLike.congr_fun h1 e[2]
  simp at h2

end Rank3

section Axis

/-- The monoid `ℕ e₁ ⊆ ℤ²` with the first coordinate as degree. -/
def axisDegrees : PositiveDegrees (Fin 2 → ℤ) where
  monoid :=
    { carrier := {n | 0 ≤ n 0 ∧ n 1 = 0}
      zero_mem' := ⟨le_rfl, rfl⟩
      add_mem' := fun {a b} ha hb => ⟨add_nonneg ha.1 hb.1, by simp [ha.2, hb.2]⟩ }
  degree := Pi.evalAddMonoidHom (fun _ => ℤ) 0
  degree_pos {n} hn hne := by
    refine lt_of_le_of_ne hn.1 fun h => hne ?_
    ext i
    fin_cases i
    · exact h.symm
    · exact hn.2
  finite_le k := by
    refine ((Set.finite_Icc (0 : ℤ) k).image fun a => ![a, 0]).subset ?_
    rintro n ⟨⟨h0, h1⟩, hk⟩
    refine ⟨n 0, ⟨h0, hk⟩, ?_⟩
    ext i
    fin_cases i <;> simp [h1]

@[simp]
theorem mem_axisDegrees_monoid {n : Fin 2 → ℤ} :
    n ∈ axisDegrees.monoid ↔ 0 ≤ n 0 ∧ n 1 = 0 :=
  Iff.rfl

/-- The first basis vector is an allowed degree of `ℕ e₁`. -/
theorem single_zero_mem_axisDegrees : (Pi.single 0 1 : Fin 2 → ℤ) ∈ axisDegrees.monoid := by
  simp

/-- The field `z^{e₁} ∂_{e₂*}` of the tropical vertex Lie algebra of `ℕ e₁ ⊆ ℤ²`. -/
def axisField : tropicalVertexLieAlgebra (R := ℚ) axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) :=
  ⟨single (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 0 1) (coordinate 1),
    single_mem_tropicalVertexLieAlgebra _ _ single_zero_mem_axisDegrees (by simp) _ (by simp)⟩

/-- The field `z^{e₁} ∂_{e₂*}` is nonzero in the tropical vertex Lie algebra. -/
theorem axisField_ne_zero : axisField ≠ 0 := by
  intro h
  have h1 := single_injective (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 0 1)
    ((congrArg Subtype.val h).trans (map_zero _).symm)
  have h2 := DFunLike.congr_fun h1 (Pi.single 1 1)
  simp at h2

/-- The nonzero field `z^{e₁} ∂_{e₂*}` acts by zero on the coefficient algebra of `ℕ e₁`. -/
theorem tropicalVertexCoefficientAction_axisField :
    tropicalVertexCoefficientAction axisDegrees (AddMonoidHom.id (Fin 2 → ℤ))
      axisDegrees.monoid le_rfl axisField = 0 := by
  have h : (coordinate 1 : (Fin 2 → ℤ) →+ ℚ).comp
      ((AddMonoidHom.id (Fin 2 → ℤ)).comp axisDegrees.monoid.subtype) = 0 :=
    AddMonoidHom.ext fun p => by simp [p.2.2]
  rw [axisField, tropicalVertexCoefficientAction_single axisDegrees _ _ le_rfl
    single_zero_mem_axisDegrees (by simp) _ (by simp), h, map_zero]

end Axis

section Sum

/-- The coordinate sum `(a, b) ↦ a + b` from `ℕ²` to `ℕ` is a positive degree map. -/
def sumDegreeMap :
    PositiveDegreeMap (PositiveDegrees.orthant (Fin 2)) PositiveDegrees.nonnegIntegers :=
  PositiveDegreeMap.ofBound (PositiveDegrees.orthant (Fin 2)).degree
    (fun n hn => by
      simpa [Fin.sum_univ_two] using add_nonneg (PositiveDegrees.mem_orthant_monoid.mp hn 0)
        (PositiveDegrees.mem_orthant_monoid.mp hn 1))
    1 (fun n _ => by simp)

@[simp]
theorem sumDegreeMap_apply (n : Fin 2 → ℤ) : sumDegreeMap n = n 0 + n 1 := by
  simp [sumDegreeMap, Fin.sum_univ_two]

/-- No tropical pairing has the coordinate sum as its degree map, on any space of
characters containing `e₁*`: the degrees `(1, 0)` and `(0, 1)` have the same image
but different `e₁*`-values. -/
theorem degreeMap_ne_sumDegreeMap {U : Submodule ℚ ((Fin 2 → ℤ) →+ ℚ)}
    (hU : coordinate 0 ∈ U)
    (p : TropicalPairing (d := PositiveDegrees.orthant (Fin 2))
      (e := PositiveDegrees.nonnegIntegers) (ρ := AddMonoidHom.id (Fin 2 → ℤ))
      (ρ' := AddMonoidHom.id ℤ) U) :
    p.degreeMap.toAddMonoidHom ≠ sumDegreeMap.toAddMonoidHom := by
  intro h
  have key : ∀ i : Fin 2, p.characterMap ⟨coordinate 0, hU⟩ (sumDegreeMap (Pi.single i 1)) =
      coordinate 0 (Pi.single i 1) := fun i => by
    have := p.eval_eq ⟨coordinate 0, hU⟩ (n := Pi.single i 1)
      (PositiveDegrees.single_mem_orthant_monoid i)
    rwa [AddMonoidHom.id_apply, AddMonoidHom.id_apply, DFunLike.congr_fun h] at this
  have h0 : p.characterMap ⟨coordinate 0, hU⟩ 1 = 1 := by simpa using key 0
  have h1 : p.characterMap ⟨coordinate 0, hU⟩ 1 = 0 := by simpa using key 1
  exact one_ne_zero (h0.symm.trans h1)

/-- There is no derivation of `ℚ[z]` intertwining `y x ∂_x` on `ℚ[x, y]` with the substitution
`x, y ↦ z`: it would vanish on `x - y ↦ 0`, whereas `y x ∂_x (x - y) = x y ↦ z²`. -/
theorem not_exists_derivation_intertwining :
    ¬ ∃ D : Derivation ℚ ℚ[X] ℚ[X], ∀ f : MvPolynomial (Fin 2) ℚ,
      D (MvPolynomial.aeval (fun _ => (X : ℚ[X])) f) =
        MvPolynomial.aeval (fun _ => (X : ℚ[X]))
          (MvPolynomial.X 1 * MvPolynomial.X 0 * MvPolynomial.pderiv 0 f) := by
  rintro ⟨D, hD⟩
  have h := hD (MvPolynomial.X 0 - MvPolynomial.X 1)
  simp at h

end Sum

section Double

/-- The doubling `(a, b) ↦ (2 a, b)` of `ℤ²`. -/
def doubleFirst : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  AddMonoidHom.mk' (fun n => ![2 * n 0, n 1]) fun a b => by
    ext i
    fin_cases i
    · simp; ring
    · simp

@[simp]
theorem doubleFirst_apply (n : Fin 2 → ℤ) : doubleFirst n = ![2 * n 0, n 1] := (rfl)

/-- Doubling the first coordinate is a positive degree map of `ℕ²` to itself. -/
def doubleFirstDegreeMap :
    PositiveDegreeMap (PositiveDegrees.orthant (Fin 2)) (PositiveDegrees.orthant (Fin 2)) :=
  PositiveDegreeMap.ofBound doubleFirst
    (fun n hn => by
      have := PositiveDegrees.mem_orthant_monoid.mp hn
      refine PositiveDegrees.mem_orthant_monoid.mpr fun i => ?_
      fin_cases i
      · simpa using this 0
      · simpa using this 1)
    1 (fun n hn => by
      have := PositiveDegrees.mem_orthant_monoid.mp hn
      have := this 0
      simp [Fin.sum_univ_two]
      omega)

@[simp]
theorem doubleFirstDegreeMap_apply (n : Fin 2 → ℤ) : doubleFirstDegreeMap n = ![2 * n 0, n 1] := by
  simp [doubleFirstDegreeMap]

/-- The rational inverse dual of the doubling: it sends a character `m` to `m ∘ T⁻¹`, where
`T⁻¹ (a, b) = (a / 2, b)`. -/
def inverseDualDouble : ((Fin 2 → ℤ) →+ ℚ) →ₗ[ℚ] ((Fin 2 → ℤ) →+ ℚ) where
  toFun m := (m (Pi.single 0 1) / 2) • coordinate 0 + m (Pi.single 1 1) • coordinate 1
  map_add' m m' := AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
    ring
  map_smul' c m := AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The doubling of the first coordinate with its rational inverse dual is a tropical
pairing on the space of all characters. -/
def doublePairing :
    TropicalPairing (d := PositiveDegrees.orthant (Fin 2)) (e := PositiveDegrees.orthant (Fin 2))
      (ρ := AddMonoidHom.id (Fin 2 → ℤ)) (ρ' := AddMonoidHom.id (Fin 2 → ℤ))
      (⊤ : Submodule ℚ ((Fin 2 → ℤ) →+ ℚ)) where
  degreeMap := doubleFirstDegreeMap
  characterMap := inverseDualDouble.comp (Submodule.subtype _)
  eval_eq m n _ := by
    simp only [AddMonoidHom.id_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [AddMonoidHom.apply_pi_eq_sum_zsmul m.val n]
    simp [inverseDualDouble, Fin.sum_univ_two]
    ring

/-- The pairing of the doubling sends `z^{e₂} ∂_{e₁*}` to `(1/2) z^{e₂} ∂_{e₁*}`. -/
theorem doublePairing_gradedLieHom_single :
    (doublePairing.gradedLieHom (tropicalSingle
      (PositiveDegrees.orthant (Fin 2)) (AddMonoidHom.id (Fin 2 → ℤ)) ⊤
      (n := Pi.single 1 1) (PositiveDegrees.single_mem_orthant_monoid 1) (by simp)
      ⟨coordinate 0, trivial⟩
      (by simp))).val =
      (1 / 2 : ℚ) • single (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 1 1) (coordinate 0) := by
  have hT : doublePairing.degreeMap (Pi.single 1 1) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [doublePairing]
  have hS : doublePairing.characterMap ⟨coordinate 0, trivial⟩ = (1 / 2 : ℚ) • coordinate 0 :=
    AddMonoidHom.ext fun x => by simp [doublePairing, inverseDualDouble]
  rw [TropicalPairing.coe_gradedLieHom_tropicalSingle, hT, hS, map_smul]

end Double

end Mei.LogarithmicVectorField.Examples
