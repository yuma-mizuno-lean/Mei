/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.Convex.Polyhedron.Rational.Halfspace

/-!
# Orientation data and rational polyhedra of the standard plane

The plane `ℝ × ℝ` carries the standard lattice `ℤ × ℤ`. This file records the data needed to
write explicit oriented cells there: the coordinate form `dy` and the area form `dx ∧ dy`, whose
rays orient the normal quotients of lines and points; the horizontal direction, which is the
direction of every horizontal line or segment through the origin; and the rational-normal
polyhedra cut out by the coordinate functionals, namely the upper half-plane, the horizontal axis
and the closed unit segment on the axis.
-/

public section

open Set Module Mei.FinitePolyhedralComplex

namespace Mei.Plane

/-- The constant alternating `0`-form `1`, which orients the plane's full-dimensional cells. -/
def constOne : (ℝ × ℝ) [⋀^Fin 0]→ₗ[ℝ] ℝ := AlternatingMap.constOfIsEmpty ℝ (ℝ × ℝ) (Fin 0) 1

@[simp]
theorem constOne_apply (v : Fin 0 → ℝ × ℝ) : constOne v = 1 := (rfl)

/-- The constant `0`-form `1` is nonzero. -/
theorem constOne_ne_zero : constOne ≠ 0 := fun h0 => by
  simpa using congrArg (fun f : (ℝ × ℝ) [⋀^Fin 0]→ₗ[ℝ] ℝ => f ![]) h0

/-- The coordinate form `dy` of the plane, as an alternating `1`-form. -/
def dy : (ℝ × ℝ) [⋀^Fin 1]→ₗ[ℝ] ℝ :=
  AlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ 0 (LinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem dy_apply (v : Fin 1 → ℝ × ℝ) : dy v = (v 0).2 := (rfl)

/-- The form `dy` is nonzero. -/
theorem dy_ne_zero : dy ≠ 0 := fun h0 => by
  simpa using congrArg (fun f : (ℝ × ℝ) [⋀^Fin 1]→ₗ[ℝ] ℝ => f ![(0, 1)]) h0

/-- The area form `dx ∧ dy` of the plane, the determinant in the standard basis. -/
noncomputable def area : (ℝ × ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ := (Basis.finTwoProd ℝ).det

/-- The area form is the determinant of the two arguments. -/
theorem area_apply (v : Fin 2 → ℝ × ℝ) :
    area v = (v 0).1 * (v 1).2 - (v 0).2 * (v 1).1 := by
  simp only [area, Basis.det_apply, Matrix.det_fin_two, Basis.toMatrix_apply]
  simp
  ring

/-- The area form is nonzero. -/
theorem area_ne_zero : area ≠ 0 := fun h0 => by
  simpa [area_apply] using congrArg (fun f : (ℝ × ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ => f ![(1, 0), (0, 1)]) h0

/-- The horizontal direction: the kernel of the second coordinate. -/
def horizontal : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem mem_horizontal {v : ℝ × ℝ} : v ∈ horizontal ↔ v.2 = 0 := Iff.rfl

/-- The horizontal direction is a line. -/
theorem finrank_horizontal : finrank ℝ horizontal = 1 := by
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.snd ℝ ℝ ℝ)
  rw [LinearMap.range_eq_top.mpr LinearMap.snd_surjective, finrank_top] at this
  simp only [finrank_self, finrank_prod] at this
  rw [horizontal]
  omega

/-- A subset of the horizontal axis containing `(0, 0)` and `(1, 0)` spans the horizontal
direction. -/
theorem vectorSpan_eq_horizontal {A : Set (ℝ × ℝ)} (hA : ∀ p ∈ A, p.2 = 0) (h0 : (0, 0) ∈ A)
    (h1 : (1, 0) ∈ A) : vectorSpan ℝ A = horizontal := by
  refine le_antisymm ?_ fun v hv => ?_
  · rw [vectorSpan_def]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, hp, q, hq, rfl⟩
    simp [horizontal, hA p hp, hA q hq]
  · have hv2 : v.2 = 0 := hv
    have : v = v.1 • ((1, 0) - (0, 0) : ℝ × ℝ) := by ext <;> simp [hv2]
    rw [this]
    exact Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ h1 h0)

/-- The form `dy` is conormal to the horizontal direction. -/
theorem dy_mem_conormalForms : dy ∈ horizontal.conormalForms (Fin 1) :=
  Submodule.mem_conormalForms.mpr fun v j hv => by
    rwa [Fin.fin_one_eq_zero j] at hv

/-- The upper half-plane spans the whole plane. -/
theorem vectorSpan_upperHalfPlane : vectorSpan ℝ {p : ℝ × ℝ | 0 ≤ p.2} = ⊤ := by
  have h1 : ((1, 0) : ℝ × ℝ) - (0, 0) ∈ vectorSpan ℝ {p : ℝ × ℝ | 0 ≤ p.2} :=
    vsub_mem_vectorSpan ℝ (by simp) (by simp)
  have h2 : ((0, 1) : ℝ × ℝ) - (0, 0) ∈ vectorSpan ℝ {p : ℝ × ℝ | 0 ≤ p.2} :=
    vsub_mem_vectorSpan ℝ (by simp) (by simp)
  refine eq_top_iff.mpr fun v _ => ?_
  have : v = v.1 • ((1, 0) - (0, 0) : ℝ × ℝ) + v.2 • ((0, 1) - (0, 0) : ℝ × ℝ) := by
    ext <;> simp
  exact this ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

/-- The upper half-plane is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_upperHalfPlane
    (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))) :
    IsRationalNormalPolyhedron h {p : ℝ × ℝ | 0 ≤ p.2} := by
  convert isRationalNormalPolyhedron_setOf_le (-axisRow true)
    (by simpa using (isRationalFunctional_axisRow h true).neg) 0 using 1
  ext p
  simp

/-- The horizontal axis is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_axis
    (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))) :
    IsRationalNormalPolyhedron h {p : ℝ × ℝ | p.2 = 0} := by
  convert (isRationalNormalPolyhedron_upperHalfPlane h).inter
    (isRationalNormalPolyhedron_setOf_le (axisRow true)
      (isRationalFunctional_axisRow h true) 0) using 1
  ext p
  simp [le_antisymm_iff, and_comm]

/-- The closed segment from `(0, 0)` to `(1, 0)` consists of the points of the axis with
first coordinate in `[0, 1]`. -/
theorem mem_segment_iff {p : ℝ × ℝ} :
    p ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0) ↔ p.2 = 0 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1 := by
  refine ⟨?_, fun ⟨h2, h0, h1⟩ => ⟨1 - p.1, p.1, by linarith, h0, by ring, ?_⟩⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨by simp, by simpa using hb, ?_⟩
    simpa using (by linarith : b ≤ 1)
  · ext <;> simp [h2]

/-- The closed unit segment on the axis is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_segment
    (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))) :
    IsRationalNormalPolyhedron h (segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0)) := by
  convert ((isRationalNormalPolyhedron_axis h).inter
    (isRationalNormalPolyhedron_setOf_le (-axisRow false)
      (by simpa using (isRationalFunctional_axisRow h false).neg) 0)).inter
    (isRationalNormalPolyhedron_setOf_le (axisRow false)
      (isRationalFunctional_axisRow h false) 1) using 1
  ext p
  simp [mem_segment_iff, and_assoc]

end Mei.Plane
