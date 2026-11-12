/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basis
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.TropicalPairing
public import Mathlib.GroupTheory.IndexNSmul

/-!
# Pushing a vertical wall along `(a, b) ↦ (2a, b)`

On the positive quadrant `P = ℕ²` of `ℤ²`, with identity projection to the plane `ℝ²`, the
embedding `T (a, b) = (2a, b)` has image of finite index, since it contains `2ℤ²`, and is a
positive degree map with identity cutoff modulus (`doubleFirstDegreeMap`). With the integral
normal map `ν m = m ∘ (x, y) ↦ (x, 2y)`, which satisfies `ν m ∘ T = 2 • m`, it gives
`DirectedWall.Pushforward.ofFiniteIndex` data (`doubleFirstPushforward`) for the integral
lattice `ℤ² ⊆ ℝ²`. Hence the hypotheses of the finite-index pushforward hold in this case.

* The normal `e₁*` is kept: `ν e₁* = e₁*` (`doubleSecondNormal_fst`).
* The field `z^{e₂} ∂_{e₁*}` is sent to `(1/2) z^{e₂} ∂_{e₁*}`: the rational inverse dual
  of `e₁*` is `(1/2) e₁*`, and the denominator goes into the label
  (`coe_doubleFirstPushforward_lieHom_single`).
* The vertical axis `{x = 0}`, a wall on the ray `e₂` with normal `e₁*` and any label, is
  pushed to an incoming wall with the same normal
  (`verticalAxis_pushforward_normal`, `verticalAxis_pushforward_incoming`).

The tropical pairing of the rational inverse dual of a finite-index embedding is Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegreeMap)

noncomputable section

namespace Mei.DirectedWall.Pushforward.Examples

open LogarithmicVectorField TauCeti.Toric

/-- The positive quadrant `ℕ²` of `ℤ²`, with coordinate-sum degree. -/
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

local notation "ρ₀" => AddMonoidHom.id (ℤ × ℤ)

/-- The embedding `(a, b) ↦ (2a, b)` of `ℤ²`. -/
def doubleFirst : ℤ × ℤ →+ ℤ × ℤ :=
  (AddMonoidHom.mulLeft (2 : ℤ)).prodMap (AddMonoidHom.id ℤ)

/-- `T (a, b) = (2a, b)`. -/
@[simp]
theorem doubleFirst_apply (x : ℤ × ℤ) : doubleFirst x = (2 * x.1, x.2) := (rfl)

/-- The embedding `(a, b) ↦ (2a, b)` is injective. -/
theorem doubleFirst_injective : Function.Injective doubleFirst := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [doubleFirst_apply, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- The image of `(a, b) ↦ (2a, b)` contains `2 ℤ²`, so it has finite index. -/
instance : doubleFirst.range.FiniteIndex := by
  have : (nsmulAddMonoidHom (α := ℤ × ℤ) 2).range.FiniteIndex :=
    ⟨by rw [AddSubgroup.index_range_nsmul]; norm_num⟩
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (α := ℤ × ℤ) 2).range) ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(x.1, 2 * x.2), by ext <;> simp [two_mul]⟩

/-- The embedding `(a, b) ↦ (2a, b)` as a positive degree map of the quadrant, with identity
cutoff modulus. -/
def doubleFirstDegreeMap : PositiveDegreeMap ℕ² ℕ² :=
  PositiveDegreeMap.ofBound doubleFirst
    (fun n hn => by
      simp [Fin.forall_fin_two] at hn ⊢
      omega)
    1 (fun n hn => by
      simp [Fin.forall_fin_two] at hn ⊢
      omega)

/-- The positive degree map is `(a, b) ↦ (2a, b)`. -/
@[simp]
theorem doubleFirstDegreeMap_apply (x : ℤ × ℤ) : doubleFirstDegreeMap x = (2 * x.1, x.2) := by
  simp [doubleFirstDegreeMap]

/-- With identity projections, the degree map and the tangent embedding agree. -/
theorem doubleFirstDegreeMap_eq_doubleFirst (n : ℤ × ℤ) (_ : n ∈ ℕ².monoid) :
    ρ₀ (doubleFirstDegreeMap n) = doubleFirst (ρ₀ n) := by
  simp

/-- The integral normal map `m ↦ m ∘ ((x, y) ↦ (x, 2y))`. -/
def doubleSecondNormal (m : ℤ × ℤ →+ ℤ) : ℤ × ℤ →+ ℤ :=
  m.comp ((AddMonoidHom.id ℤ).prodMap (AddMonoidHom.mulLeft (2 : ℤ)))

/-- `ν m (x, y) = m (x, 2y)`. -/
@[simp]
theorem doubleSecondNormal_apply (m : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    doubleSecondNormal m x = m (x.1, 2 * x.2) := (rfl)

/-- The normal map restricts along `(a, b) ↦ (2a, b)` to twice the original normal. -/
theorem doubleSecondNormal_apply_doubleFirst (m : ℤ × ℤ →+ ℤ) (x : ℤ × ℤ) :
    (doubleSecondNormal m (doubleFirst x) : ℚ) = 2 * m x := by
  have hx : ((2 * x.1, 2 * x.2) : ℤ × ℤ) = (2 : ℤ) • x := by ext <;> simp
  rw [doubleSecondNormal_apply, doubleFirst_apply, hx, map_zsmul, smul_eq_mul, Int.cast_mul,
    Int.cast_ofNat]

/-- The normal `e₁*` is kept. -/
@[simp]
theorem doubleSecondNormal_fst : doubleSecondNormal (AddMonoidHom.fst ℤ ℤ) = AddMonoidHom.fst ℤ ℤ :=
  AddMonoidHom.ext fun _ => rfl

variable (h : IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- Pushforward data along `(a, b) ↦ (2a, b)` between the tropical vertex wall spaces of the
quadrant over `ℚ`, with normals `m ↦ m ∘ ((x, y) ↦ (x, 2y))` and comparison scalar `2`. -/
def doubleFirstPushforward :
    Pushforward ℕ² ℕ² h h (tropicalVertexWallSpaces (R := ℚ) ℕ² ρ₀)
      (tropicalVertexWallSpaces ℕ² ρ₀) :=
  ofFiniteIndex doubleFirstDegreeMap doubleFirst doubleFirst_injective
    doubleFirstDegreeMap_eq_doubleFirst doubleSecondNormal (fun _ => 2) (fun _ => two_pos)
    doubleSecondNormal_apply_doubleFirst

/-- The basis vector `e₂ = (0, 1)` is an allowed degree. -/
theorem zero_one_mem : ((0 : ℤ), (1 : ℤ)) ∈ ℕ².monoid := by
  simp [Fin.forall_fin_two]

/-- The field `z^{e₂} ∂_{e₁*}` is sent to `(1/2) z^{e₂} ∂_{e₁*}`. -/
theorem coe_doubleFirstPushforward_lieHom_single :
    ((doubleFirstPushforward h).lieHom
        ⟨single ρ₀ (0, 1) ((Int.castAddHom ℚ).comp (AddMonoidHom.fst ℤ ℤ)),
          single_mem_tropicalVertexLieAlgebra ℕ² ρ₀ zero_one_mem (by simp) _ (by simp)⟩).val =
      (1 / 2 : ℚ) • single ρ₀ (0, 1) ((Int.castAddHom ℚ).comp (AddMonoidHom.fst ℤ ℤ)) := by
  have he := coe_ofFiniteIndex_lieHom_single (R := ℚ) (ρ := ρ₀) (ρ' := ρ₀)
    (h := h) (h' := h) doubleFirstDegreeMap doubleFirst
    doubleFirst_injective doubleFirstDegreeMap_eq_doubleFirst doubleSecondNormal (fun _ => 2)
    (fun _ => two_pos) doubleSecondNormal_apply_doubleFirst zero_one_mem (by simp)
    (AddMonoidHom.fst ℤ ℤ) (by simp)
  rw [doubleFirstDegreeMap_apply, doubleSecondNormal_fst, mul_zero, Algebra.algebraMap_self,
    RingHom.id_apply] at he
  rw [doubleFirstPushforward, he, one_div]

section VerticalAxis

variable (g : (tropicalVertexWallSpaces (R := ℚ) ℕ² ρ₀).wallGroup
  (Module.Basis.positiveDegreesRay (Module.Basis.finTwoProd ℤ) 1) (AddMonoidHom.fst ℤ ℤ))

/-- The vertical axis `{x = 0}` of `ℝ²` as a wall on the ray `e₂`, with normal `e₁*`. -/
def verticalAxis : DirectedWall (d := ℕ²) h (tropicalVertexWallSpaces (R := ℚ) ℕ² ρ₀) :=
  ofAffineHyperplane _ _ (AddMonoidHom.fst ℤ ℤ)
    (fun he => by simpa using DFunLike.congr_fun he (1, 0)) 0 _ (by simp) g

/-- The pushed vertical axis keeps the normal `e₁*`. -/
theorem verticalAxis_pushforward_normal :
    ((verticalAxis h g).pushforward (doubleFirstPushforward h)).normal = AddMonoidHom.fst ℤ ℤ := by
  simp [verticalAxis, doubleFirstPushforward]

/-- The pushed vertical axis is incoming, since the vertical axis is. -/
theorem verticalAxis_pushforward_incoming :
    ((verticalAxis h g).pushforward (doubleFirstPushforward h)).Incoming :=
  (incoming_pushforward_iff _ _).mpr (ofAffineHyperplane_incoming ..)

end VerticalAxis

end Mei.DirectedWall.Pushforward.Examples
