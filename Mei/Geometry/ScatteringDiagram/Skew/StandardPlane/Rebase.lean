/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.UnitFactor
public import Mei.Algebra.Lie.Skew.Map

/-!
# Rescaling the standard plane along two plane degrees

For plane degrees `x, y` with `D = {y, x} > 0`, the change of basis `e₁ ↦ y`, `e₂ ↦ x` carries
the plane with weights `(δ y, δ x)` to the plane with weight `w` and multiplies the skew
pairing by `D`. It is a positive degree map with the same cutoff, and `X_n ↦ D⁻¹ X_{T n}` is a
graded map of the positive skew Lie algebras. At every order it carries the dilogarithm label
`Ψ[m]^c` of the rescaled plane to `Ψ[T m]^{c / D}`, hence products of unit factors of the
rescaled plane to products of the labels `Ψ[T m]^{κ(m) / D}`. This reduces the exchange of `x`
and `y` to the pair `e₂, e₁` of the rescaled plane.
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples PowerSeries

local notation "β" => E.coefficientForm ℚ
local notation "hβ" => E.isAlt_coefficientForm ℚ

variable {w : Weight}

/-- The weights `(δ y, δ x)` of the plane rescaled along the plane degrees `x, y`. -/
def Weight.rebase (x y : PlaneDegree w) : Weight where
  fst := y.deg
  snd := x.deg
  fst_pos := y.deg_pos
  snd_pos := x.deg_pos

@[simp]
theorem Weight.fst_rebase (x y : PlaneDegree w) : (Weight.rebase x y).fst = y.deg := (rfl)

@[simp]
theorem Weight.snd_rebase (x y : PlaneDegree w) : (Weight.rebase x y).snd = x.deg := (rfl)

/-- The change of basis `e₁ ↦ y`, `e₂ ↦ x` of the plane. -/
def rebase (x y : Γ) : Γ →+ Γ where
  toFun v := v.1.1 • y + v.1.2 • x
  map_zero' := by simp
  map_add' v v' := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel

@[simp]
theorem rebase_fst (x y v : Γ) : (rebase x y v).1.1 = v.1.1 * y.1.1 + v.1.2 * x.1.1 := by
  simp [rebase]

@[simp]
theorem rebase_snd (x y v : Γ) : (rebase x y v).1.2 = v.1.1 * y.1.2 + v.1.2 * x.1.2 := by
  simp [rebase]

variable (x y : PlaneDegree w)

theorem degree_rebase (v : Γ) :
    (plane w).degree (rebase x.vec y.vec v) = (plane (Weight.rebase x y)).degree v := by
  rw [plane_degree, plane_degree, rebase_fst, rebase_snd]
  have hx := x.deg_eq
  have hy := y.deg_eq
  simp only [Weight.rebase]
  linear_combination (-v.1.1) * hy + (-v.1.2) * hx

theorem rebase_mem {v : Γ} (hv : v ∈ (plane (Weight.rebase x y)).monoid) :
    rebase x.vec y.vec v ∈ (plane w).monoid := by
  rw [mem_plane_monoid] at hv ⊢
  rw [rebase_fst, rebase_snd]
  exact ⟨add_nonneg (mul_nonneg hv.1 y.fst_nonneg) (mul_nonneg hv.2 x.fst_nonneg),
    add_nonneg (mul_nonneg hv.1 y.snd_nonneg) (mul_nonneg hv.2 x.snd_nonneg)⟩

/-- The rescaling `e₁ ↦ y`, `e₂ ↦ x` is a positive degree map from the plane with weights
`(δ y, δ x)` to the plane with weight `w`, with the same cutoff. -/
def rebaseMap : PositiveDegreeMap (plane (Weight.rebase x y)) (plane w) :=
  PositiveDegreeMap.ofBound (rebase x.vec y.vec) (fun _ hv => rebase_mem x y hv) 1
    (fun v _ => by rw [Nat.cast_one, one_mul, degree_rebase])

theorem form_rebase (v v' : Γ) :
    E.coefficientForm ℚ (rebase x.vec y.vec v) (rebase x.vec y.vec v') =
      (x.det y : ℚ) * E.coefficientForm ℚ v v' := by
  rw [coefficientForm_apply, coefficientForm_apply, PlaneDegree.det_eq, rebase_fst, rebase_snd,
    rebase_fst, rebase_snd]
  push_cast
  ring

@[simp]
theorem rebaseMap_apply (v : Γ) : rebaseMap x y v = rebase x.vec y.vec v :=
  PositiveDegreeMap.ofBound_apply _ _ _ _ v

/-- The image of a plane degree of the rescaled plane under the change of basis. -/
def rebasePos (m : PlaneDegree (Weight.rebase x y)) : PlaneDegree w where
  vec := rebaseMap x y m.vec
  mem := (rebaseMap x y).map_mem m.mem
  ne_zero := (rebaseMap x y).map_ne_zero m.mem m.ne_zero

@[simp]
theorem rebasePos_vec (m : PlaneDegree (Weight.rebase x y)) :
    (rebasePos x y m).vec = rebase x.vec y.vec m.vec := rebaseMap_apply x y m.vec

theorem rebasePos_fst (m : PlaneDegree (Weight.rebase x y)) :
    (rebasePos x y m).fst = m.fst * y.fst + m.snd * x.fst := by
  simp [PlaneDegree.fst, PlaneDegree.snd]

theorem rebasePos_snd (m : PlaneDegree (Weight.rebase x y)) :
    (rebasePos x y m).snd = m.fst * y.snd + m.snd * x.snd := by
  simp [PlaneDegree.fst, PlaneDegree.snd]

/-- The image of `e₂` under the rescaling along `x, y` is `x`. -/
theorem rebasePos_e₂ : rebasePos x y (PlaneDegree.e₂ (Weight.rebase x y)) = x := by
  refine PlaneDegree.ext (Subtype.ext (Prod.ext ?_ ?_)) <;> simp [rebasePos_vec]

/-- The image of `e₁` under the rescaling along `x, y` is `y`. -/
theorem rebasePos_e₁ : rebasePos x y (PlaneDegree.e₁ (Weight.rebase x y)) = y := by
  refine PlaneDegree.ext (Subtype.ext (Prod.ext ?_ ?_)) <;> simp [rebasePos_vec]

/-- The rescaling preserves weighted degrees. -/
theorem deg_rebasePos (m : PlaneDegree (Weight.rebase x y)) : (rebasePos x y m).deg = m.deg := by
  apply Nat.cast_injective (R := ℤ)
  rw [PlaneDegree.deg_eq_degree, PlaneDegree.deg_eq_degree, rebasePos_vec, degree_rebase]

variable {x y}

theorem coefficientForm_eq_inv_mul_rebaseMap (hD : x.det y ≠ 0) (n m : Γ) :
    E.coefficientForm ℚ n m =
      (x.det y : ℚ)⁻¹ * E.coefficientForm ℚ (rebaseMap x y n) (rebaseMap x y m) := by
  rw [rebaseMap_apply, rebaseMap_apply, form_rebase, ← mul_assoc,
    inv_mul_cancel₀ (Int.cast_ne_zero.mpr hD), one_mul]

variable (x y)

theorem rebaseMap_modulus_le (k : ℕ) : (rebaseMap x y).modulus k ≤ k := by
  rw [rebaseMap, PositiveDegreeMap.ofBound_modulus]
  omega

/-- The finite-order projection of a ray label of the rescaled plane, carried to the plane by the
rescaling, is the projection of the ray label of the image degree with exponent divided by
`{y, x}`. -/
theorem map_projection_dilogPow (hD : x.det y ≠ 0) (k : ℕ) (m : PlaneDegree (Weight.rebase x y))
    (c : ℚ) :
    ((SkewLieAlgebra.gradedMap β hβ β hβ (x.det y : ℚ)⁻¹ (rebaseMap x y)
          (coefficientForm_eq_inv_mul_rebaseMap hD)).truncatedMap k
        (rebaseMap_modulus_le x y k)).bchGroupMap
        (CompletedGroup.projection k (dilogPow m c)) =
      CompletedGroup.projection k (dilogPow (rebasePos x y m) ((x.det y : ℚ)⁻¹ * c)) := by
  rw [dilogPow_def, dilogPow_def, mul_smul]
  exact SkewLieAlgebra.truncatedMap_gradedMap_projection_rayExp β hβ β hβ (x.det y : ℚ)⁻¹
    (rebaseMap x y) (coefficientForm_eq_inv_mul_rebaseMap hD) m.mem m.ne_zero
    (c • negDilogNeg ℚ) k k (rebaseMap_modulus_le x y k)

/-- **Transport of identities between unit factors.** An identity at order `k` between products
of unit factors of the rescaled plane gives the same identity in the plane between the
products of the labels `Ψ[T m]^{κ(m) / D}`, where `D = {y, x}`. -/
theorem projection_prod_rebasePos_eq (hD : x.det y ≠ 0) (k : ℕ)
    {L₁ L₂ : List (PlaneDegree (Weight.rebase x y))}
    (h : CompletedGroup.projection k (L₁.map unitFactor).prod =
      CompletedGroup.projection k (L₂.map unitFactor).prod) :
    CompletedGroup.projection k
        (L₁.map fun m => dilogPow (rebasePos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod =
      CompletedGroup.projection k
        (L₂.map fun m => dilogPow (rebasePos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod := by
  let ψ := ((SkewLieAlgebra.gradedMap β hβ β hβ (x.det y : ℚ)⁻¹ (rebaseMap x y)
    (coefficientForm_eq_inv_mul_rebaseMap hD)).truncatedMap k
      (rebaseMap_modulus_le x y k)).bchGroupMap
  have key : ∀ L : List (PlaneDegree (Weight.rebase x y)),
      ψ (CompletedGroup.projection k (L.map unitFactor).prod) =
      CompletedGroup.projection k
        (L.map fun m => dilogPow (rebasePos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.prod_nil, map_one (CompletedGroup.projection k)]
      exact map_one ψ
    | cons m L ih =>
      have h1 : ψ (CompletedGroup.projection k (unitFactor m)) = CompletedGroup.projection k
          (dilogPow (rebasePos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)) := by
        rw [unitFactor_def]
        exact map_projection_dilogPow x y hD k m _
      simp only [List.map_cons, List.prod_cons, map_mul (CompletedGroup.projection k)]
      exact (map_mul ψ _ _).trans (congrArg₂ (· * ·) h1 ih)
  rw [← key, ← key, h]

end Mei.StandardPlane
