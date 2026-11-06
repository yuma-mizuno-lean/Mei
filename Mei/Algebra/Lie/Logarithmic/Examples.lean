/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.WallFunction.Binomial
public import Mei.Algebra.MonoidAlgebra.Filtration.PowerSeries
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Examples for the tropical vertex Lie algebra

Four small computations delimit the Lie algebra of formal logarithmic derivations `z^n ∂_m`
over `ℚ`, its tropical pairings and their action on binomial labels.

* In rank three the degree-`e₁` piece contains the independent fields `z^{e₁} ∂_{e₂*}` and
  `z^{e₁} ∂_{e₃*}`, and the bracket of `z^{e₁} ∂_{e₃*}` with `z^{e₂} ∂_{e₁*}` is the nonzero
  field `-z^{e₁+e₂} ∂_{e₃*}`, although `e₃*(e₂) = 0`: only the term `e₁*(e₁) = 1` survives.
* For the monoid `ℕ e₁ ⊆ ℤ²` the nonzero field `z^{e₁} ∂_{e₂*}` acts by zero on the coefficient
  algebra of the monoid, since every allowed degree has vanishing second coordinate. A field is
  therefore not determined by its action on this coefficient algebra.
* The coordinate sum `(a, b) ↦ a + b` from `ℕ²` to `ℕ` is a positive degree map, but it admits
  no tropical pairing on any character space containing `e₁*`: the degrees `(1, 0)` and
  `(0, 1)` have the same image and different `e₁*`-values. Correspondingly, there is no
  derivation of `ℚ[z]` intertwining `y x ∂_x` on `ℚ[x, y]` with the substitution `x, y ↦ z`.
* On `ℕ e₁ ⊆ ℤ²` precomposition with `(a, b) ↦ (a, -b)` is a tropical pairing on all
  characters sending `e₂*` to `-e₂*`. It sends the binomial label
  `exp(log(1 + c z^{e₁}) ∂_{e₂*})` to its inverse, which for `c ≠ 0` is a different element of the
  completed tropical vertex group; the label acts trivially on the coefficient algebra of `ℕ e₁`.

The Lie algebra of logarithmic derivations and the pairing condition are those of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.LogarithmicVectorField.Examples

open _root_.AddMonoidAlgebra Polynomial
open scoped Mei.TropicalVertexCoefficientAction

/-- The `i`-th coordinate character of `ℤ^ι` with values in `ℚ`. -/
def coordinate {ι : Type*} (i : ι) : (ι → ℤ) →+ ℚ :=
  (Int.castAddHom ℚ).comp (Pi.evalAddMonoidHom (fun _ => ℤ) i)

@[simp]
theorem coordinate_apply {ι : Type*} (i : ι) (n : ι → ℤ) : coordinate i n = n i := (rfl)

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
  have h1 := DFunLike.congr_fun (single_injective ρ₃ e[0] h0)
  exact ⟨by simpa using h1 e[1], by simpa using h1 e[2]⟩

/-- For `i ≠ 0` the field `z^{e₁} ∂_{e_i*}` lies in the tropical vertex Lie algebra of `ℕ³`. -/
theorem single_coordinate_mem_tropicalVertexLieAlgebra {i : Fin 3} (hi : i ≠ 0) :
    single ρ₃ e[0] (coordinate i) ∈
      tropicalVertexLieAlgebra (R := ℚ) (PositiveDegrees.orthant (Fin 3)) ρ₃ :=
  single_mem_tropicalVertexLieAlgebra _ _
    (PositiveDegrees.mem_orthant_monoid.mpr fun j => by rw [Pi.single_apply]; split_ifs <;> simp)
    (by simp) _ (by simp [hi.symm])

/-- The bracket of `z^{e₁} ∂_{e₃*}` with `z^{e₂} ∂_{e₁*}` is `-z^{e₁+e₂} ∂_{e₃*}`, even though
`e₃*(e₂) = 0`. -/
theorem bracket_single_coordinate :
    ⁅single ρ₃ e[0] (coordinate 2), single ρ₃ e[1] (coordinate 0)⁆ =
      -single ρ₃ (e[0] + e[1]) (coordinate 2) := by
  rw [single_bracket_single, ← map_neg]
  congr 1
  ext n
  simp

/-- The bracket of `z^{e₁} ∂_{e₃*}` with `z^{e₂} ∂_{e₁*}` is nonzero. -/
theorem bracket_single_coordinate_ne_zero :
    ⁅single ρ₃ e[0] (coordinate 2), single ρ₃ e[1] (coordinate 0)⁆ ≠ 0 := by
  rw [bracket_single_coordinate, neg_ne_zero]
  intro h
  have h1 := DFunLike.congr_fun (single_injective ρ₃ _ (h.trans (map_zero _).symm)) e[2]
  simp at h1

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

/-- The allowed degrees of `ℕ e₁` are the vectors with nonnegative first and vanishing second
coordinate. -/
@[simp]
theorem mem_axisDegrees_monoid {n : Fin 2 → ℤ} :
    n ∈ axisDegrees.monoid ↔ 0 ≤ n 0 ∧ n 1 = 0 :=
  Iff.rfl

/-- The degree of `ℕ e₁` is the first coordinate. -/
@[simp]
theorem axisDegrees_degree (n : Fin 2 → ℤ) : axisDegrees.degree n = n 0 := (rfl)

/-- The first basis vector is an allowed degree of `ℕ e₁`. -/
theorem single_zero_mem_axisDegrees : (Pi.single 0 1 : Fin 2 → ℤ) ∈ axisDegrees.monoid := by
  simp

/-- The field `z^{e₁} ∂_{e₂*}` of the tropical vertex Lie algebra of `ℕ e₁ ⊆ ℤ²`. -/
def axisField : tropicalVertexLieAlgebra (R := ℚ) axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) :=
  ⟨single (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 0 1) (coordinate 1),
    single_mem_tropicalVertexLieAlgebra _ _ single_zero_mem_axisDegrees (by simp) _ (by simp)⟩

/-- The underlying logarithmic vector field of `axisField` is `z^{e₁} ∂_{e₂*}`. -/
@[simp]
theorem coe_axisField : (axisField : LogarithmicVectorField ℚ (Fin 2 → ℤ) (Fin 2 → ℤ)
    (AddMonoidHom.id (Fin 2 → ℤ))) = single (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 0 1)
      (coordinate 1) := (rfl)

/-- The field `z^{e₁} ∂_{e₂*}` is nonzero in the tropical vertex Lie algebra. -/
theorem axisField_ne_zero : axisField ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun (single_injective (AddMonoidHom.id (Fin 2 → ℤ)) (Pi.single 0 1)
    ((congrArg Subtype.val h).trans (map_zero _).symm)) (Pi.single 1 1)
  simp at h1

/-- The nonzero field `z^{e₁} ∂_{e₂*}` acts by zero on the coefficient algebra of `ℕ e₁`. -/
@[simp]
theorem tropicalVertexCoefficientAction_axisField :
    tropicalVertexCoefficientAction axisDegrees (AddMonoidHom.id (Fin 2 → ℤ))
      axisDegrees.monoid le_rfl axisField = 0 := by
  have h : (coordinate 1).comp ((AddMonoidHom.id (Fin 2 → ℤ)).comp
      axisDegrees.monoid.subtype) = 0 :=
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

/-- No tropical pairing has the coordinate sum as its degree map, on any space of characters
containing `e₁*`: the degrees `(1, 0)` and `(0, 1)` have the same image but different
`e₁*`-values. -/
theorem degreeMap_ne_sumDegreeMap {U : Submodule ℚ ((Fin 2 → ℤ) →+ ℚ)}
    (hU : coordinate 0 ∈ U)
    (p : TropicalPairing (d := PositiveDegrees.orthant (Fin 2))
      (e := PositiveDegrees.nonnegIntegers) (ρ := AddMonoidHom.id (Fin 2 → ℤ))
      (ρ' := AddMonoidHom.id ℤ) U) :
    p.degreeMap.toAddMonoidHom ≠ sumDegreeMap.toAddMonoidHom := by
  intro h
  have key (i : Fin 2) : p.characterMap ⟨coordinate 0, hU⟩ (sumDegreeMap (Pi.single i 1)) =
      coordinate 0 (Pi.single i 1) := by
    have := p.eval_eq ⟨coordinate 0, hU⟩ (n := Pi.single i 1)
      (PositiveDegrees.mem_orthant_monoid.mpr fun j => by
        rw [Pi.single_apply]; split_ifs <;> simp)
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

section Sign

/-- Reversing the second coordinate of `ℤ²`. -/
def negSecond : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  AddMonoidHom.mk' (fun n => ![n 0, -n 1]) fun a b => by
    ext i
    fin_cases i <;> simp [add_comm]

@[simp]
theorem negSecond_apply (n : Fin 2 → ℤ) : negSecond n = ![n 0, -n 1] := (rfl)

/-- Precomposition with the reversal of the second coordinate is a tropical pairing of `ℕ e₁`
with itself on all characters. It fixes every allowed degree and sends `e₂*` to `-e₂*`. -/
def signPairing :
    TropicalPairing (d := axisDegrees) (e := axisDegrees)
      (ρ := AddMonoidHom.id (Fin 2 → ℤ)) (ρ' := AddMonoidHom.id (Fin 2 → ℤ))
      (⊤ : Submodule ℚ ((Fin 2 → ℤ) →+ ℚ)) where
  degreeMap := PositiveDegreeMap.id axisDegrees
  characterMap :=
    { toFun := fun m => m.val.comp negSecond
      map_add' := fun _ _ => AddMonoidHom.ext fun _ => by simp
      map_smul' := fun _ _ => AddMonoidHom.ext fun _ => by simp }
  eval_eq m n hn := by
    have : negSecond n = n := by
      ext i
      fin_cases i <;> simp [hn.2]
    simp [this]

@[simp]
theorem signPairing_degreeMap : signPairing.degreeMap = PositiveDegreeMap.id axisDegrees := (rfl)

@[simp]
theorem signPairing_characterMap (m : (⊤ : Submodule ℚ ((Fin 2 → ℤ) →+ ℚ))) :
    signPairing.characterMap m = m.val.comp negSecond := (rfl)

/-- The coordinate character `e₂*` of `ℤ²` with integer values. -/
local notation "μ₂" => Pi.evalAddMonoidHom (fun _ : Fin 2 => ℤ) 1

/-- The sign pairing sends the binomial label `exp(log(1 + c z^{e₁}) ∂_{e₂*})` to its inverse. -/
@[simp]
theorem completedMap_signPairing_binomialLabel (c : ℚ) :
    signPairing.tropicalVertexGradedLieHom.completedMap
        (binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
          single_zero_mem_axisDegrees (by simp) (by simp) c) =
      (binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
        single_zero_mem_axisDegrees (by simp) (by simp) c)⁻¹ := by
  rw [← binomialLabel_neg single_zero_mem_axisDegrees (by simp) (by simp)]
  refine signPairing.completedMap_binomialLabel (μ' := -μ₂) ?_ _ _ _ _ _ _ ?_ _
  · ext x
    simp
  · simp

local instance : Fact (axisDegrees.monoid ≤ axisDegrees.monoid) := ⟨le_rfl⟩

/-- The binomial label `exp(log(1 + c z^{e₁}) ∂_{e₂*})` acts trivially on every monomial of the
completed coefficient algebra of `ℕ e₁`, since `e₂*` vanishes on `ℕ e₁`. -/
@[simp]
theorem completedBCHAction_binomialLabel_axis (c : ℚ) (p : axisDegrees.monoid) :
    (TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
        axisDegrees.monoid).completedBCHAction axisDegrees
      (tropicalVertexGrading (R := ℚ) axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)))
      (binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
        single_zero_mem_axisDegrees (by simp) (by simp) c)
      ((TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
        axisDegrees.monoid).toCompletion (AddMonoidAlgebra.single p 1)) =
    (TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
        axisDegrees.monoid).toCompletion (AddMonoidAlgebra.single p 1) := by
  rw [completedBCHAction_binomialLabel]
  simp [p.property.2]

/-- The half-plane `{(a, b) ∈ ℤ² | 0 ≤ a}`, a coefficient monoid containing `ℕ e₁` and both
`±e₂`. -/
def rightHalfPlane : AddSubmonoid (Fin 2 → ℤ) where
  carrier := {n | 0 ≤ n 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by simpa using add_nonneg (a := a 0) (b := b 0) ha hb

@[simp]
theorem mem_rightHalfPlane {n : Fin 2 → ℤ} : n ∈ rightHalfPlane ↔ 0 ≤ n 0 := Iff.rfl

local instance : Fact (axisDegrees.monoid ≤ rightHalfPlane) := ⟨fun _ h => by simpa using h.1⟩

/-- For `c ≠ 0` the binomial label `exp(log(1 + c z^{e₁}) ∂_{e₂*})` is not its own inverse in the
completed tropical vertex group of `ℕ e₁`. Hence the inversion by the sign pairing is not
vacuous. -/
theorem binomialLabel_ne_inv {c : ℚ} (hc : c ≠ 0) :
    binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
      single_zero_mem_axisDegrees (by simp) (by simp) c ≠
    (binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
      single_zero_mem_axisDegrees (by simp) (by simp) c)⁻¹ := by
  -- Proof plan: if the label were its own inverse, its action and the action of its inverse on the
  -- completed coefficient algebra of the half-plane `{0 ≤ a}` would agree. This gives
  -- `a * a + 2 * a = 0` modulo the filtration ideal for the monomial `a = c z^{e₁}`, and the
  -- coefficient of `z^{e₁}` in it is `2 * c`.
  intro h
  have hn : (Pi.single 0 1 : Fin 2 → ℤ) ∈ axisDegrees.monoid := single_zero_mem_axisDegrees
  let p : rightHalfPlane := ⟨Pi.single 1 1, by simp⟩
  have k₁ := completedBCHAction_binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) μ₂
    rightHalfPlane hn (by simp) (by simp) c p 1
  have k₂ := completedBCHAction_binomialLabel axisDegrees (AddMonoidHom.id (Fin 2 → ℤ)) (-μ₂)
    rightHalfPlane hn (by simp) (by simp) c p 1
  rw [binomialLabel_neg hn (by simp) (by simp), ← h] at k₂
  have ht : IsUnit ((TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
      rightHalfPlane).toCompletion (AddMonoidAlgebra.single p 1)) :=
    TropicalVertexCoefficientAction.isUnit_toCompletion_single (e := axisDegrees)
      (P := rightHalfPlane) (p := Pi.single 1 1) (by simp) (by simp)
  have k := (ht.mul_left_inj).mp (k₁.symm.trans k₂)
  simp only [Fin.isValue, AddMonoidHom.id_apply, Pi.evalAddMonoidHom_apply, Pi.single_eq_same,
    zpow_ofNat, pow_one, coe_binomialUnit, AddMonoidHom.neg_apply, Int.reduceNeg, zpow_neg,
    p] at k
  have hu := (binomialUnit axisDegrees rightHalfPlane hn (by simp) c).mul_inv
  rw [← k, coe_binomialUnit] at hu
  set a : (ℚ)[rightHalfPlane] := AddMonoidAlgebra.single ⟨Pi.single 0 1, by simp⟩ c with ha
  have h2 : (TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
      rightHalfPlane).toCompletion (a * a + 2 * a) = 0 := by
    simp only [map_add, map_mul, map_ofNat]
    linear_combination hu
  have h3 : a * a + 2 * a ∈ (TropicalVertexCoefficientAction.filtration (R := ℚ) axisDegrees
      rightHalfPlane).ideal 2 := by
    rw [← AlgFiltration.toCompletion_mem_completionIdeal_iff, h2]
    exact zero_mem _
  rw [TropicalVertexCoefficientAction.filtration_ideal] at h3
  have hcoeff : (a * a + 2 * a).coeff ⟨Pi.single 0 1, by simp⟩ = 2 * c := by
    rw [two_mul, ← add_assoc, ha, single_mul_single]
    simp [two_mul]
  have h4 := AddSubmonoid.coeff_eq_zero_of_mem_monoidAlgebraIdeal (δ :=
    axisDegrees.degree.comp rightHalfPlane.subtype) _ (fun q => q.property) h3
    (p := ⟨Pi.single 0 1, by simp⟩) (k := 2) (by simp)
  rw [hcoeff] at h4
  exact hc (by simpa using h4)

end Sign

end Mei.LogarithmicVectorField.Examples
