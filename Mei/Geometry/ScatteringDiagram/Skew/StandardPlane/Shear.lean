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
def Weight.shear (x y : PlaneDegree w) : Weight where
  fst := y.deg
  snd := x.deg
  fst_pos := y.deg_pos
  snd_pos := x.deg_pos

@[simp]
theorem Weight.fst_shear (x y : PlaneDegree w) : (Weight.shear x y).fst = y.deg := (rfl)

@[simp]
theorem Weight.snd_shear (x y : PlaneDegree w) : (Weight.shear x y).snd = x.deg := (rfl)

/-- The change of basis `e₁ ↦ y`, `e₂ ↦ x` of the plane. -/
def shear (x y : Γ) : Γ →+ Γ where
  toFun v := v.1.1 • y + v.1.2 • x
  map_zero' := by simp
  map_add' v v' := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, add_smul]
    abel

@[simp]
theorem shear_fst (x y v : Γ) : (shear x y v).1.1 = v.1.1 * y.1.1 + v.1.2 * x.1.1 := by
  simp [shear]

@[simp]
theorem shear_snd (x y v : Γ) : (shear x y v).1.2 = v.1.1 * y.1.2 + v.1.2 * x.1.2 := by
  simp [shear]

variable (x y : PlaneDegree w)

theorem degree_shear (v : Γ) :
    (plane w).degree (shear x.vec y.vec v) = (plane (Weight.shear x y)).degree v := by
  rw [plane_degree, plane_degree, shear_fst, shear_snd]
  have hx := x.deg_eq
  have hy := y.deg_eq
  simp only [Weight.shear]
  linear_combination (-v.1.1) * hy + (-v.1.2) * hx

theorem shear_mem {v : Γ} (hv : v ∈ (plane (Weight.shear x y)).monoid) :
    shear x.vec y.vec v ∈ (plane w).monoid := by
  rw [mem_plane_monoid] at hv ⊢
  rw [shear_fst, shear_snd]
  exact ⟨add_nonneg (mul_nonneg hv.1 y.fst_nonneg) (mul_nonneg hv.2 x.fst_nonneg),
    add_nonneg (mul_nonneg hv.1 y.snd_nonneg) (mul_nonneg hv.2 x.snd_nonneg)⟩

/-- The rescaling `e₁ ↦ y`, `e₂ ↦ x` is a positive degree map from the plane with weights
`(δ y, δ x)` to the plane with weight `w`, with the same cutoff. -/
def sheared : PositiveDegreeMap (plane (Weight.shear x y)) (plane w) :=
  PositiveDegreeMap.ofBound (shear x.vec y.vec) (fun _ hv => shear_mem x y hv) 1
    (fun v _ => by rw [Nat.cast_one, one_mul, degree_shear])

theorem form_shear (v v' : Γ) :
    E.coefficientForm ℚ (shear x.vec y.vec v) (shear x.vec y.vec v') =
      (x.det y : ℚ) * E.coefficientForm ℚ v v' := by
  rw [coefficientForm_apply, coefficientForm_apply, PlaneDegree.det_eq, shear_fst, shear_snd,
    shear_fst, shear_snd]
  push_cast
  ring

@[simp]
theorem sheared_apply (v : Γ) : sheared x y v = shear x.vec y.vec v :=
  PositiveDegreeMap.ofBound_apply _ _ _ _ v

/-- The image of a plane degree of the rescaled plane under the change of basis. -/
def shearPos (m : PlaneDegree (Weight.shear x y)) : PlaneDegree w where
  vec := sheared x y m.vec
  mem := (sheared x y).map_mem m.mem
  ne_zero := (sheared x y).map_ne_zero m.mem m.ne_zero

@[simp]
theorem shearPos_vec (m : PlaneDegree (Weight.shear x y)) :
    (shearPos x y m).vec = shear x.vec y.vec m.vec := sheared_apply x y m.vec

theorem shearPos_fst (m : PlaneDegree (Weight.shear x y)) :
    (shearPos x y m).fst = m.fst * y.fst + m.snd * x.fst := by
  simp [PlaneDegree.fst, PlaneDegree.snd]

theorem shearPos_snd (m : PlaneDegree (Weight.shear x y)) :
    (shearPos x y m).snd = m.fst * y.snd + m.snd * x.snd := by
  simp [PlaneDegree.fst, PlaneDegree.snd]

/-- The image of `e₂` under the rescaling along `x, y` is `x`. -/
theorem shearPos_e₂ : shearPos x y (PlaneDegree.e₂ (Weight.shear x y)) = x := by
  refine PlaneDegree.ext (Subtype.ext (Prod.ext ?_ ?_)) <;> simp [shearPos_vec]

/-- The image of `e₁` under the rescaling along `x, y` is `y`. -/
theorem shearPos_e₁ : shearPos x y (PlaneDegree.e₁ (Weight.shear x y)) = y := by
  refine PlaneDegree.ext (Subtype.ext (Prod.ext ?_ ?_)) <;> simp [shearPos_vec]

/-- The rescaling preserves weighted degrees. -/
theorem deg_shearPos (m : PlaneDegree (Weight.shear x y)) : (shearPos x y m).deg = m.deg := by
  apply Nat.cast_injective (R := ℤ)
  rw [PlaneDegree.deg_eq_degree, PlaneDegree.deg_eq_degree, shearPos_vec, degree_shear]

variable {x y}

theorem hform_shear (hD : x.det y ≠ 0) (n m : Γ) :
    E.coefficientForm ℚ n m =
      (x.det y : ℚ)⁻¹ * E.coefficientForm ℚ (sheared x y n) (sheared x y m) := by
  rw [sheared_apply, sheared_apply, form_shear, ← mul_assoc,
    inv_mul_cancel₀ (Int.cast_ne_zero.mpr hD), one_mul]

variable (x y)

theorem sheared_modulus_le (k : ℕ) : (sheared x y).modulus k ≤ k := by
  rw [sheared, PositiveDegreeMap.ofBound_modulus]
  omega

/-- The finite-order projection of a ray label of the rescaled plane, carried to the plane by the
rescaling, is the projection of the ray label of the image degree with exponent divided by
`{y, x}`. -/
theorem map_projection_dilogPow (hD : x.det y ≠ 0) (k : ℕ) (m : PlaneDegree (Weight.shear x y))
    (c : ℚ) :
    ((SkewLieAlgebra.gradedMap β hβ β hβ (x.det y : ℚ)⁻¹ (sheared x y)
          (hform_shear hD)).truncatedMap k (sheared_modulus_le x y k)).bchGroupMap
        (CompletedGroup.projection k (dilogPow m c)) =
      CompletedGroup.projection k (dilogPow (shearPos x y m) ((x.det y : ℚ)⁻¹ * c)) := by
  rw [dilogPow_def, dilogPow_def, mul_smul]
  exact SkewLieAlgebra.truncatedMap_gradedMap_projection_rayExp β hβ β hβ (x.det y : ℚ)⁻¹
    (sheared x y) (hform_shear hD) m.mem m.ne_zero (c • negDilogNeg ℚ) k k
    (sheared_modulus_le x y k)

/-- **Transport of identities between unit factors.** An identity at order `k` between products
of unit factors of the rescaled plane gives the same identity in the plane between the
products of the labels `Ψ[T m]^{κ(m) / D}`, where `D = {y, x}`. -/
theorem projection_prod_shearPos_eq (hD : x.det y ≠ 0) (k : ℕ)
    {L₁ L₂ : List (PlaneDegree (Weight.shear x y))}
    (h : CompletedGroup.projection k (L₁.map unitFactor).prod =
      CompletedGroup.projection k (L₂.map unitFactor).prod) :
    CompletedGroup.projection k
        (L₁.map fun m => dilogPow (shearPos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod =
      CompletedGroup.projection k
        (L₂.map fun m => dilogPow (shearPos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod := by
  let ψ := ((SkewLieAlgebra.gradedMap β hβ β hβ (x.det y : ℚ)⁻¹ (sheared x y)
    (hform_shear hD)).truncatedMap k (sheared_modulus_le x y k)).bchGroupMap
  have key : ∀ L : List (PlaneDegree (Weight.shear x y)),
      ψ (CompletedGroup.projection k (L.map unitFactor).prod) =
      CompletedGroup.projection k
        (L.map fun m => dilogPow (shearPos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)).prod := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.prod_nil, map_one (CompletedGroup.projection k)]
      exact map_one ψ
    | cons m L ih =>
      have h1 : ψ (CompletedGroup.projection k (unitFactor m)) = CompletedGroup.projection k
          (dilogPow (shearPos x y m) ((x.det y : ℚ)⁻¹ * rayIndex m.vec)) := by
        rw [unitFactor_def]
        exact map_projection_dilogPow x y hD k m _
      simp only [List.map_cons, List.prod_cons, map_mul (CompletedGroup.projection k)]
      exact (map_mul ψ _ _).trans (congrArg₂ (· * ·) h1 ih)
  rw [← key, ← key, h]

end Mei.StandardPlane
