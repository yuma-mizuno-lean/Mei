/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Analysis.Convex.Polyhedron.Image
public import Mei.Geometry.Convex.PolyhedralCochain.Plane.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.AffineImage.Basic

/-!
# Images of the quadrant and a sheared strip

In the plane `ℝ × ℝ` with the standard lattice `ℤ × ℤ`, and on `ℝ` with the lattice `ℤ`:

* the sum map `(x, y) ↦ x + y` has rational linear part (`isRationalLinearMap_sumMap`) and is not
  injective on the closed quadrant `{0 ≤ x, 0 ≤ y}` (`not_injOn_sumMap_quadrant`), so the image of
  the quadrant is covered by `Mei.IsRationalNormalPolyhedron.affine_image` but not by
  `Mei.IsLocallyClosedPolyhedron.image_of_injOn`. The image is rational-normal
  (`isRationalNormalPolyhedron_image_sumMap_quadrant`), and it is the ray `[0, ∞)`
  (`image_sumMap_quadrant`);
* the map `(x, y) ↦ x + √2 y` has irrational linear part; the image of the quadrant is still a
  convex polyhedron (`isConvexPolyhedron_image_sqrtTwoMap_quadrant`);
* adding the diagonal line `ℝ ∙ (1, 1)` to the unit segment `[(0, 0), (1, 0)]` gives the
  rational-normal strip `{0 ≤ x - y ≤ 1}` (`segment_add_span_diagonal`,
  `isRationalNormalPolyhedron_segment_add_span_diagonal`).
-/

public section

open scoped Pointwise

open Set TauCeti.Toric Mei.FinitePolyhedralComplex

namespace Mei.IsRationalNormalPolyhedron.Examples

/-- The standard lattice `ℤ × ℤ ⊆ ℝ × ℝ`. -/
theorem isIntegralLattice_plane :
    IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)) :=
  isIntegralLattice_castAddHom.prod isIntegralLattice_castAddHom

/-- The closed quadrant `{0 ≤ x, 0 ≤ y}`. -/
def quadrant : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

/-- A point lies in the quadrant exactly when both coordinates are nonnegative. -/
@[simp]
theorem mem_quadrant {p : ℝ × ℝ} : p ∈ quadrant ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 := Iff.rfl

/-- The quadrant is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_quadrant :
    IsRationalNormalPolyhedron isIntegralLattice_plane quadrant := by
  convert (isRationalNormalPolyhedron_setOf_le (-axisRow false)
    (by simpa using (isRationalFunctional_axisRow isIntegralLattice_plane false).neg) 0).inter
    (isRationalNormalPolyhedron_setOf_le (-axisRow true)
      (by simpa using (isRationalFunctional_axisRow isIntegralLattice_plane true).neg) 0)
    using 1
  ext p
  simp

/-- The sum of the two coordinates, as an affine map `ℝ × ℝ → ℝ`. -/
def sumMap : ℝ × ℝ →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap

/-- The sum map adds the two coordinates. -/
@[simp]
theorem sumMap_apply (p : ℝ × ℝ) : sumMap p = p.1 + p.2 := (rfl)

/-- The linear part of the sum map is the sum of the coordinate projections. -/
@[simp]
theorem linear_sumMap : sumMap.linear = LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ := (rfl)

/-- The sum map is rational: it extends the integral map `(a, b) ↦ a + b`. -/
theorem isRationalLinearMap_sumMap :
    Toric.IsRationalLinearMap isIntegralLattice_plane isIntegralLattice_castAddHom
      sumMap.linear :=
  Toric.IsRationalLinearMap.of_integral_compatible _ _
    (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ) _ fun n => by simp

/-- The sum map is not injective on the quadrant: `(1, 0)` and `(0, 1)` have the same sum. -/
theorem not_injOn_sumMap_quadrant : ¬ InjOn sumMap quadrant := fun hinj => by
  have := hinj (x₁ := (1, 0)) (x₂ := (0, 1)) (by simp) (by simp) (by simp)
  simp at this

/-- The image of the quadrant under the sum map is a rational-normal polyhedron in `ℝ`. -/
theorem isRationalNormalPolyhedron_image_sumMap_quadrant :
    IsRationalNormalPolyhedron isIntegralLattice_castAddHom (sumMap '' quadrant) :=
  isRationalNormalPolyhedron_quadrant.affine_image sumMap isRationalLinearMap_sumMap

/-- The image of the quadrant under the sum map is the ray `[0, ∞)`. -/
theorem image_sumMap_quadrant : sumMap '' quadrant = Ici 0 := by
  ext t
  simp only [mem_image, mem_quadrant, sumMap_apply, mem_Ici]
  constructor
  · rintro ⟨p, ⟨h₁, h₂⟩, rfl⟩
    positivity
  · intro ht
    exact ⟨(t, 0), ⟨ht, le_rfl⟩, add_zero t⟩

/-- The continuous linear map `(x, y) ↦ x + √2 y`, whose linear part is not rational. -/
noncomputable def sqrtTwoMap : ℝ × ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ + √2 • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The map `sqrtTwoMap` sends `(x, y)` to `x + √2 y`. -/
@[simp]
theorem sqrtTwoMap_apply (p : ℝ × ℝ) : sqrtTwoMap p = p.1 + √2 * p.2 := (rfl)

/-- The image of the quadrant under `(x, y) ↦ x + √2 y` is a convex polyhedron. -/
theorem isConvexPolyhedron_image_sqrtTwoMap_quadrant :
    TauCeti.IsConvexPolyhedron (sqrtTwoMap '' quadrant) :=
  isRationalNormalPolyhedron_quadrant.isConvexPolyhedron.affine_image
    sqrtTwoMap.toContinuousAffineMap

/-- The lattice vector `(1, 1)` is the real point `(1, 1)`. -/
theorem prodMap_one_one :
    (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ) ((1, 1) : ℤ × ℤ) = ((1, 1) : ℝ × ℝ) := by
  simp

/-- Adding the diagonal line `ℝ ∙ (1, 1)` to the unit segment on the horizontal axis gives the
strip `{0 ≤ x - y ≤ 1}`. -/
theorem segment_add_span_diagonal :
    segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) + ((ℝ ∙ ((1, 1) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) :
      Set (ℝ × ℝ)) = {p | 0 ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 1} := by
  ext p
  simp only [Submodule.mem_add_span_singleton_iff, Plane.mem_segment_zero_one_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨a, h₂, h₀, h₁⟩
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_one] at h₂ h₀ h₁
    constructor <;> linarith
  · rintro ⟨h₀, h₁⟩
    exact ⟨-p.2, by simp, by simpa [← sub_eq_add_neg] using h₀,
      by simpa [← sub_eq_add_neg] using h₁⟩

/-- The strip `{0 ≤ x - y ≤ 1}`, obtained by adding the diagonal line to the unit segment, is a
rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_segment_add_span_diagonal :
    IsRationalNormalPolyhedron isIntegralLattice_plane
      (segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) +
        ((ℝ ∙ ((1, 1) : ℝ × ℝ) : Submodule ℝ (ℝ × ℝ)) : Set (ℝ × ℝ))) := by
  rw [← prodMap_one_one]
  exact (Plane.isRationalNormalPolyhedron_segment isIntegralLattice_plane).add_span_singleton
    ((1, 1) : ℤ × ℤ)

end Mei.IsRationalNormalPolyhedron.Examples
