/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Logarithmic.WallFunction.Binomial
public import Mei.Algebra.Lie.Logarithmic.Faithful
public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Algebra.Ring.Units
public import Mei.Algebra.Group.Units.Hom

/-!
# The pentagon identity in the tropical vertex group

Let `n₁, n₂` be nonzero allowed degrees and `μ₁, μ₂` integral characters of the spatial lattice
with `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`, `μ₁(ρ n₂) = -1` and `μ₂(ρ n₁) = 1`. Write `θ[μ, n, c]` for the
binomial label `exp(log(1 + c z^n) ∂_μ)` (`Mei.binomialLabel`). For all coefficients `c₁, c₂` the
completed tropical vertex group satisfies the pentagon identity
`θ[μ₂, n₂, c₂] θ[μ₁, n₁, c₁] = θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂] θ[μ₂, n₂, c₂]`
(`Mei.binomialLabel_pentagon`); the case of the coordinate vectors of the quadrant `ℕ² ⊆ ℤ²` is
`Mei.binomialLabel_pentagon_quadrant`. No condition on the positive degree data, on the spatial
projection `ρ` or on the coefficients is imposed beyond these pairings; the degrees and lattices
live in `Type`.

The *quadrant pairing* of `n₁, n₂, μ₁, μ₂` (`Mei.quadrantPairing`) is the tropical pairing from
the nonnegative quadrant of `ℤ × ℤ` given by the positive degree map `(a, b) ↦ a n₁ + b n₂` and
the character map `m ↦ m(1, 0) μ₂ - m(0, 1) μ₁` (`Mei.quadrantCharacterMap`), which pairs with
`ρ(a n₁ + b n₂)` as `m` pairs with `(a, b)` (`Mei.quadrantCharacterMap_apply_constr`).

This is the pentagon identity of the tropical vertex group of Gross–Pandharipande–Siebert,
*Quivers, curves, and the tropical vertex*, Example 1.6 (arXiv:0902.0779v3), here with
coefficients and in the formulation of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra Module
open scoped TropicalVertexCoefficientAction

section Quadrant

variable {R : Type*} [CommRing R] [Algebra ℚ R]

local notation "b" => Basis.finTwoProd ℤ
local notation "𝒅" => Basis.positiveDegrees (Basis.finTwoProd ℤ)
local notation "ℒ₀" => tropicalVertexGrading (R := R) 𝒅 (AddMonoidHom.id (ℤ × ℤ))
local notation "F₀" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅
  (PositiveDegrees.monoid 𝒅)

/-- **Pentagon identity on the quadrant.** In the tropical vertex group of the nonnegative quadrant
`ℕ² ⊆ ℤ²`, with the identity spatial projection, write `e₁ = (1, 0)`, `e₂ = (0, 1)`,
`μ₁ = -e₂*` and `μ₂ = e₁*`. For all coefficients `c₁, c₂` the binomial labels satisfy
`θ[μ₂, e₂, c₂] θ[μ₁, e₁, c₁] = θ[μ₁, e₁, c₁] θ[μ₁ + μ₂, e₁ + e₂, c₁ c₂] θ[μ₂, e₂, c₂]`. -/
theorem binomialLabel_pentagon_quadrant (c₁ c₂ : R) :
    binomialLabel 𝒅 (AddMonoidHom.id _) (AddMonoidHom.fst ℤ ℤ)
        ((b).mem_positiveDegrees_monoid_self 1) ((b).ne_zero 1) (by simp) c₂ *
      binomialLabel 𝒅 (AddMonoidHom.id _) (-AddMonoidHom.snd ℤ ℤ)
        ((b).mem_positiveDegrees_monoid_self 0) ((b).ne_zero 0) (by simp) c₁ =
    binomialLabel 𝒅 (AddMonoidHom.id _) (-AddMonoidHom.snd ℤ ℤ)
        ((b).mem_positiveDegrees_monoid_self 0) ((b).ne_zero 0) (by simp) c₁ *
      binomialLabel 𝒅 (AddMonoidHom.id _) (-AddMonoidHom.snd ℤ ℤ + AddMonoidHom.fst ℤ ℤ)
        (add_mem ((b).mem_positiveDegrees_monoid_self 0)
          ((b).mem_positiveDegrees_monoid_self 1))
        ((𝒅).add_ne_zero ((b).mem_positiveDegrees_monoid_self 0)
          ((b).mem_positiveDegrees_monoid_self 1) ((b).ne_zero 0)) (by simp) (c₁ * c₂) *
      binomialLabel 𝒅 (AddMonoidHom.id _) (AddMonoidHom.fst ℤ ℤ)
        ((b).mem_positiveDegrees_monoid_self 1) ((b).ne_zero 1) (by simp) c₂ := by
  classical
  have : Fact ((𝒅).monoid ≤ (𝒅).monoid) := ⟨le_rfl⟩
  -- Compare the actions on each positive monomial `z^p`: with `x = c₁ z^{e₁}`, `y = c₂ z^{e₂}`,
  -- every factor multiplies `z^p` by an integer power of its binomial unit, and both sides
  -- multiply `z^p` by `(1 + x + x y)^a (1 + y)^b` for `a = μ₁(p)`, `b = μ₂(p)`.
  apply TropicalVertexCoefficientAction.eq_of_completedBCHAction_toCompletion_single_eq 𝒅
    (AddMonoidHom.id _) (by simpa using (b).span_tmul_positiveDegrees_monoid)
  intro p
  have W₁ := completedBCHAction_binomialLabel 𝒅 (AddMonoidHom.id _) (-AddMonoidHom.snd ℤ ℤ)
    (𝒅).monoid ((b).mem_positiveDegrees_monoid_self 0) ((b).ne_zero 0) (by simp) c₁
  have W₂ := completedBCHAction_binomialLabel 𝒅 (AddMonoidHom.id _) (AddMonoidHom.fst ℤ ℤ)
    (𝒅).monoid ((b).mem_positiveDegrees_monoid_self 1) ((b).ne_zero 1) (by simp) c₂
  have W₁₂ := completedBCHAction_binomialLabel 𝒅 (AddMonoidHom.id _)
    (-AddMonoidHom.snd ℤ ℤ + AddMonoidHom.fst ℤ ℤ) (𝒅).monoid
    (add_mem ((b).mem_positiveDegrees_monoid_self 0) ((b).mem_positiveDegrees_monoid_self 1))
    ((𝒅).add_ne_zero ((b).mem_positiveDegrees_monoid_self 0)
      ((b).mem_positiveDegrees_monoid_self 1) ((b).ne_zero 0)) (by simp) (c₁ * c₂)
  have hXY : (F₀).toCompletion (single ⟨b 0 + b 1, add_mem ((b).mem_positiveDegrees_monoid_self 0)
      ((b).mem_positiveDegrees_monoid_self 1)⟩ (c₁ * c₂)) =
      (F₀).toCompletion (single ⟨b 0, (b).mem_positiveDegrees_monoid_self 0⟩ c₁) *
        (F₀).toCompletion (single ⟨b 1, (b).mem_positiveDegrees_monoid_self 1⟩ c₂) := by
    rw [← map_mul, single_mul_single, AddSubmonoid.mk_add_mk]
  -- The normal exponents at the exponents `e₁`, `e₂` of the binomials.
  have e₁₀ : (-AddMonoidHom.snd ℤ ℤ) ((AddMonoidHom.id (ℤ × ℤ)) (b 0)) = 0 := by simp
  have e₁₁ : (-AddMonoidHom.snd ℤ ℤ) ((AddMonoidHom.id (ℤ × ℤ)) (b 1)) = -1 := by simp
  have e₂₀ : (AddMonoidHom.fst ℤ ℤ) ((AddMonoidHom.id (ℤ × ℤ)) (b 0)) = 1 := by simp
  have e₂₁ : (AddMonoidHom.fst ℤ ℤ) ((AddMonoidHom.id (ℤ × ℤ)) (b 1)) = 0 := by simp
  simp only [map_mul, AlgEquiv.mul_apply]
  simp only [W₁, W₂, W₁₂, map_mul, Mei.map_units_zpow, AddMonoidHom.add_apply]
  refine Units.pentagon (coe_binomialUnit ..) (coe_binomialUnit ..) hXY ?_ ?_ ?_ _ _ _
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, coe_binomialUnit, map_add, map_one, W₂, e₂₀]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, coe_binomialUnit, map_add, map_one, W₁, e₁₀,
      e₁₁, zero_add]
  · simp only [Units.coe_map, MonoidHom.coe_ofClass, coe_binomialUnit, map_add, map_one, map_mul,
      W₁, W₁₂, Mei.map_units_zpow, AddMonoidHom.add_apply, e₁₁, e₂₁, add_zero]

end Quadrant

section Pairing

variable {R Γ Λ : Type*} [CommRing R] [AddCommGroup Γ] [AddCommGroup Λ]

/-- The character map of the standard quadrant along integral characters `μ₁, μ₂`: a character
`m` of `ℤ × ℤ` goes to `m(1, 0) μ₂ - m(0, 1) μ₁`. -/
def quadrantCharacterMap (μ₁ μ₂ : Λ →+ ℤ) : ((ℤ × ℤ) →+ R) →ₗ[R] (Λ →+ R) where
  toFun m := m (1, 0) • (Int.castAddHom R).comp μ₂ - m (0, 1) • (Int.castAddHom R).comp μ₁
  map_add' m m' := by
    simp only [AddMonoidHom.add_apply, add_smul]
    abel
  map_smul' r m := by
    simp only [AddMonoidHom.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sub]

/-- The defining formula of `quadrantCharacterMap`. -/
@[simp]
theorem quadrantCharacterMap_apply (μ₁ μ₂ : Λ →+ ℤ) (m : (ℤ × ℤ) →+ R) :
    quadrantCharacterMap μ₁ μ₂ m =
      m (1, 0) • (Int.castAddHom R).comp μ₂ - m (0, 1) • (Int.castAddHom R).comp μ₁ :=
  (rfl)

variable {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {n₁ n₂ : Γ} {μ₁ μ₂ : Λ →+ ℤ}
  (h₁₁ : μ₁ (ρ n₁) = 0) (h₂₂ : μ₂ (ρ n₂) = 0) (h₁₂ : μ₁ (ρ n₂) = -1) (h₂₁ : μ₂ (ρ n₁) = 1)

include h₁₁ h₂₂ h₁₂ h₂₁ in
/-- If `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`, `μ₁(ρ n₂) = -1` and `μ₂(ρ n₁) = 1`, the image of a character `m`
of `ℤ × ℤ` under the quadrant character map of `μ₁, μ₂` takes the value `m(a, b)` at
`ρ(a n₁ + b n₂)`. -/
theorem quadrantCharacterMap_apply_constr (m : (ℤ × ℤ) →+ R) (n : ℤ × ℤ) :
    quadrantCharacterMap μ₁ μ₂ m (ρ (Basis.finTwoProd ℤ |>.constr ℤ ![n₁, n₂] n)) = m n := by
  have he := (Basis.finTwoProd ℤ).ext (f₁ := ((quadrantCharacterMap μ₁ μ₂ m).comp
      (ρ.comp ((Basis.finTwoProd ℤ).constr ℤ ![n₁, n₂]).toAddMonoidHom)).toIntLinearMap)
    (f₂ := m.toIntLinearMap) fun j => by
      fin_cases j <;> simp [h₁₁, h₂₂, h₁₂, h₂₁]
  exact LinearMap.congr_fun he n

variable (R) (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0)

include h₁₁ h₂₂ h₁₂ h₂₁ in
/-- The *quadrant pairing* of nonzero allowed degrees `n₁, n₂` and integral characters `μ₁, μ₂`
with `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`, `μ₁(ρ n₂) = -1` and `μ₂(ρ n₁) = 1`: the tropical pairing from the
nonnegative quadrant of `ℤ × ℤ`, with the identity spatial projection, given by the positive
degree map `(a, b) ↦ a n₁ + b n₂` and the character map `m ↦ m(1, 0) μ₂ - m(0, 1) μ₁`. -/
def quadrantPairing : TropicalPairing (R := R) (d := Basis.positiveDegrees (Basis.finTwoProd ℤ))
    (e := d) (ρ := AddMonoidHom.id (ℤ × ℤ)) (ρ' := ρ) ⊤ where
  degreeMap := (Basis.finTwoProd ℤ).positiveDegreeMap ![n₁, n₂]
    (Fin.forall_fin_two.mpr ⟨hn₁, hn₂⟩) (Fin.forall_fin_two.mpr ⟨hn₁0, hn₂0⟩)
  characterMap := quadrantCharacterMap μ₁ μ₂ ∘ₗ (⊤ : Submodule R ((ℤ × ℤ) →+ R)).subtype
  eval_eq m n _ := by
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, AddMonoidHom.id_apply,
      Basis.positiveDegreeMap_apply] using quadrantCharacterMap_apply_constr h₁₁ h₂₂ h₁₂ h₂₁ m.val n

/-- The degree map of the quadrant pairing is `(a, b) ↦ a n₁ + b n₂`. -/
@[simp]
theorem quadrantPairing_degreeMap :
    (quadrantPairing R h₁₁ h₂₂ h₁₂ h₂₁ hn₁ hn₂ hn₁0 hn₂0).degreeMap =
      (Basis.finTwoProd ℤ).positiveDegreeMap ![n₁, n₂]
        (Fin.forall_fin_two.mpr ⟨hn₁, hn₂⟩) (Fin.forall_fin_two.mpr ⟨hn₁0, hn₂0⟩) :=
  (rfl)

/-- The character map of the quadrant pairing is the quadrant character map. -/
@[simp]
theorem quadrantPairing_characterMap (m : (⊤ : Submodule R ((ℤ × ℤ) →+ R))) :
    (quadrantPairing R h₁₁ h₂₂ h₁₂ h₂₁ hn₁ hn₂ hn₁0 hn₂0).characterMap m =
      quadrantCharacterMap μ₁ μ₂ m.val :=
  (rfl)

end Pairing

/-- **Pentagon identity in the tropical vertex group.** Let `n₁, n₂` be nonzero allowed degrees
and `μ₁, μ₂` integral characters with `μ₁(ρ n₁) = μ₂(ρ n₂) = 0`, `μ₁(ρ n₂) = -1` and
`μ₂(ρ n₁) = 1`. For all coefficients `c₁, c₂`, the binomial labels
`θ[μ, n, c] = exp(log(1 + c z^n) ∂_μ)` satisfy
`θ[μ₂, n₂, c₂] θ[μ₁, n₁, c₁] = θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂] θ[μ₂, n₂, c₂]`. -/
theorem binomialLabel_pentagon {R : Type*} [CommRing R] [Algebra ℚ R] {Γ Λ : Type}
    [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Λ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)
    {n₁ n₂ : Γ} (hn₁ : n₁ ∈ d.monoid) (hn₂ : n₂ ∈ d.monoid) (hn₁0 : n₁ ≠ 0) (hn₂0 : n₂ ≠ 0)
    {μ₁ μ₂ : Λ →+ ℤ} (h₁₁ : μ₁ (ρ n₁) = 0) (h₂₂ : μ₂ (ρ n₂) = 0) (h₁₂ : μ₁ (ρ n₂) = -1)
    (h₂₁ : μ₂ (ρ n₁) = 1) (c₁ c₂ : R) :
    binomialLabel d ρ μ₂ hn₂ hn₂0 h₂₂ c₂ * binomialLabel d ρ μ₁ hn₁ hn₁0 h₁₁ c₁ =
      binomialLabel d ρ μ₁ hn₁ hn₁0 h₁₁ c₁ *
        binomialLabel d ρ (μ₁ + μ₂) (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
          (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (c₁ * c₂) *
        binomialLabel d ρ μ₂ hn₂ hn₂0 h₂₂ c₂ := by
  -- Transport the identity of the standard quadrant along the quadrant pairing: its Lie map
  -- sends each binomial label of `e₁ = (1, 0)`, `e₂ = (0, 1)` and `e₁ + e₂` to the binomial label
  -- of `n₁`, `n₂` and `n₁ + n₂`.
  let p := quadrantPairing R h₁₁ h₂₂ h₁₂ h₂₁ hn₁ hn₂ hn₁0 hn₂0
  have he₀ := (Basis.finTwoProd ℤ).mem_positiveDegrees_monoid_self 0
  have he₁ := (Basis.finTwoProd ℤ).mem_positiveDegrees_monoid_self 1
  have hT : ∀ j, p.degreeMap (Basis.finTwoProd ℤ j) = ![n₁, n₂] j := fun j => by
    simp only [p, quadrantPairing_degreeMap, Basis.positiveDegreeMap_self]
  have hA := p.completedMap_binomialLabel (μ := -AddMonoidHom.snd ℤ ℤ) (μ' := μ₁)
    (by ext x; simp [p]) he₀ ((Basis.finTwoProd ℤ).ne_zero 0)
    (by simp) hn₁ hn₁0 h₁₁ (hT 0) c₁
  have hB := p.completedMap_binomialLabel (μ := AddMonoidHom.fst ℤ ℤ) (μ' := μ₂)
    (by ext x; simp [p]) he₁ ((Basis.finTwoProd ℤ).ne_zero 1)
    (by simp) hn₂ hn₂0 h₂₂ (hT 1) c₂
  have hC := p.completedMap_binomialLabel (μ := -AddMonoidHom.snd ℤ ℤ + AddMonoidHom.fst ℤ ℤ)
    (μ' := μ₁ + μ₂) (by ext x; simp [p, add_comm]) (add_mem he₀ he₁)
    ((Basis.positiveDegrees (Basis.finTwoProd ℤ)).add_ne_zero he₀ he₁
      ((Basis.finTwoProd ℤ).ne_zero 0)) (by simp) (add_mem hn₁ hn₂) (d.add_ne_zero hn₁ hn₂ hn₁0)
    (by simp [h₁₁, h₁₂, h₂₁, h₂₂]) (by
      rw [PositiveDegreeMap.map_add, hT 0, hT 1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]) (c₁ * c₂)
  rw [← hA, ← hB, ← hC, ← map_mul, ← map_mul, ← map_mul, binomialLabel_pentagon_quadrant]

end Mei
