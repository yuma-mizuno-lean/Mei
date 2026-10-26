/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Subgroup
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central logarithms and transport defects

For a homomorphism of nilpotent rational Lie algebras with abelian kernel,
logarithm identifies the group kernel with the additive Lie kernel. Given lifts
`s, t` of lower-order endpoint transports and a crossing `X` satisfying the
lower-order transport equation, `LieHom.logDefect` is the kernel-valued logarithm
of `t⁻¹ * X * s`. Defects add under composition, negate under reversal, and change
by a coboundary when the endpoint lifts change. For a central kernel, the sum
around a closed triangle is the logarithm of its holonomy.

These are the algebraic coefficient operations needed to turn central transport
errors into additive cochains. They use Mei's `LieHom.bchGroupMap`, its kernel
description, and `Mei.bch_eq_add_of_lie_eq_zero`. No surjectivity, grading,
freeness, or finite dimensionality is required.
-/

public section

noncomputable section

namespace LieHom

open Mei BCHGroup

variable {R L L' : Type*} [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing.IsNilpotent L']
  (f : L →ₗ⁅R⁆ L')

/-- A central Lie kernel exponentiates to a central group kernel. -/
theorem ker_bchGroupMap_le_center (hc : f.ker ≤ LieAlgebra.center R L) :
    f.bchGroupMap.ker ≤ Subgroup.center (BCHGroup L) := by
  intro g hg
  have hg' : log g ∈ f.ker := by
    simpa only [ker_bchGroupMap, LieSubalgebra.mem_bchSubgroup,
      LieIdeal.mem_toLieSubalgebra] using hg
  apply Subgroup.mem_center_iff.mpr
  intro a
  simpa only [exp_log] using
    (commute_exp_of_lie_eq_zero (log a) (log g) (hc hg' (log a))).eq

/-- Multiplication within an abelian kernel is addition in logarithmic coordinates. -/
theorem log_mul_of_mem_ker_bchGroupMap [IsLieAbelian f.ker]
    (g a : BCHGroup L) (hg : g ∈ f.bchGroupMap.ker) (ha : a ∈ f.bchGroupMap.ker) :
    log (g * a) = log g + log a := by
  let x : f.ker := ⟨log g, by
    simpa only [ker_bchGroupMap, LieSubalgebra.mem_bchSubgroup,
      LieIdeal.mem_toLieSubalgebra] using hg⟩
  let y : f.ker := ⟨log a, by
    simpa only [ker_bchGroupMap, LieSubalgebra.mem_bchSubgroup,
      LieIdeal.mem_toLieSubalgebra] using ha⟩
  have hxy : ⁅(x : L), (y : L)⁆ = 0 := by
    exact congrArg (fun z : f.ker => (z : L)) (trivial_lie_zero f.ker f.ker x y)
  exact (log_mul g a).trans (bch_eq_add_of_lie_eq_zero _ _ hxy)

/-- Logarithm identifies an abelian BCH kernel with the multiplicative version
of its additive Lie kernel. -/
def kernelLogEquiv [IsLieAbelian f.ker] :
    f.bchGroupMap.ker ≃* Multiplicative f.ker where
  toFun g := Multiplicative.ofAdd ⟨log (g : BCHGroup L), by
    rw [LieHom.mem_ker, ← log_bchGroupMap, (MonoidHom.mem_ker.mp g.property), log_one]⟩
  invFun x := ⟨exp ((Multiplicative.toAdd x : f.ker) : L), by
    simp only [MonoidHom.mem_ker, bchGroupMap_exp]
    rw [LieHom.mem_ker.mp (Multiplicative.toAdd x).property, exp_zero]⟩
  left_inv g := by ext; simp
  right_inv x := by apply Multiplicative.toAdd.injective; ext; simp
  map_mul' g a := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact f.log_mul_of_mem_ker_bchGroupMap g a g.property a.property

/-- The kernel comparison is the ambient logarithm on underlying elements. -/
@[simp]
theorem coe_kernelLogEquiv [IsLieAbelian f.ker]
    (g : f.bchGroupMap.ker) :
    ((Multiplicative.toAdd (f.kernelLogEquiv g) : f.ker) : L) =
      log (g : BCHGroup L) := (rfl)

/-- The inverse kernel comparison is the ambient exponential. -/
@[simp]
theorem coe_kernelLogEquiv_symm [IsLieAbelian f.ker]
    (x : Multiplicative f.ker) :
    ((f.kernelLogEquiv).symm x : BCHGroup L) =
      exp ((Multiplicative.toAdd x : f.ker) : L) := (rfl)

/-- The logarithmic error of a crossing between two endpoint lifts, valued in the
Lie kernel. The lower-order equation supplies kernel membership. -/
def logDefect (s t X : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t) : f.ker :=
  ⟨log (t⁻¹ * X * s), by
    rw [LieHom.mem_ker, ← log_bchGroupMap]
    simp only [map_mul, map_inv, mul_assoc, hX, inv_mul_cancel, log_one]⟩

/-- The defect is the logarithm of the gauged crossing. -/
@[simp]
theorem coe_logDefect (s t X : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t) :
    (f.logDefect s t X hX : L) = log (t⁻¹ * X * s) := (rfl)

/-- A defect vanishes exactly when the crossing is the quotient of the lifts. -/
@[simp]
theorem logDefect_eq_zero_iff (s t X : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t) :
    f.logDefect s t X hX = 0 ↔ X = t * s⁻¹ := by
  rw [← Subtype.val_inj]
  constructor
  · intro he
    have he' := congrArg exp he
    simp only [coe_logDefect, exp_log, ZeroMemClass.coe_zero, exp_zero] at he'
    have he'' : X * s = t :=
      (inv_mul_eq_one.mp (by simpa only [mul_assoc] using he')).symm
    exact eq_mul_inv_of_mul_eq he''
  · intro he
    simp [he]

/-- The identity crossing with the same lift at both ends has zero defect. -/
@[simp]
theorem logDefect_one (s : BCHGroup L) :
    f.logDefect s s 1 (by simp) = 0 := by
  apply Subtype.ext
  simp

/-- Successive crossing defects add, with the second crossing on the left. -/
theorem logDefect_mul [IsLieAbelian f.ker]
    (s t u X Y : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t)
    (hY : f.bchGroupMap Y * f.bchGroupMap t = f.bchGroupMap u) :
    f.logDefect s u (Y * X) (by simp only [map_mul, mul_assoc, hX, hY]) =
      f.logDefect t u Y hY + f.logDefect s t X hX := by
  apply Subtype.ext
  simp only [LieSubmodule.coe_add, coe_logDefect]
  have he : u⁻¹ * (Y * X) * s = (u⁻¹ * Y * t) * (t⁻¹ * X * s) := by group
  rw [he]
  apply f.log_mul_of_mem_ker_bchGroupMap
  · simp only [MonoidHom.mem_ker, map_mul, map_inv, mul_assoc, hY, inv_mul_cancel]
  · simp only [MonoidHom.mem_ker, map_mul, map_inv, mul_assoc, hX, inv_mul_cancel]

/-- Reversing a crossing negates its defect. -/
@[simp]
theorem logDefect_inv (s t X : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t) :
    f.logDefect t s X⁻¹ (by rw [map_inv, ← hX]; group) =
      -f.logDefect s t X hX := by
  apply Subtype.ext
  simp only [LieSubmodule.coe_neg, coe_logDefect]
  have he : s⁻¹ * X⁻¹ * t = (t⁻¹ * X * s)⁻¹ := by group
  rw [he, log_inv]

/-- Changing the endpoint lifts by kernel exponentials changes the defect by
the difference of their additive coordinates. -/
theorem logDefect_change_lifts [IsLieAbelian f.ker]
    (s t X : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t) (a b : f.ker) :
    f.logDefect (s * exp (a : L)) (t * exp (b : L)) X
      (by simpa only [map_mul, bchGroupMap_exp, LieHom.mem_ker.mp a.property,
        LieHom.mem_ker.mp b.property, exp_zero, mul_one] using hX) =
      f.logDefect s t X hX + a - b := by
  have ha : exp (a : L) ∈ f.bchGroupMap.ker := by
    simp only [MonoidHom.mem_ker, bchGroupMap_exp, LieHom.mem_ker.mp a.property, exp_zero]
  have hb : exp (-(b : L)) ∈ f.bchGroupMap.ker := by
    simpa only [exp_neg] using f.bchGroupMap.ker.inv_mem (by
      simp only [MonoidHom.mem_ker, bchGroupMap_exp, LieHom.mem_ker.mp b.property, exp_zero])
  have hdef : t⁻¹ * X * s ∈ f.bchGroupMap.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, mul_assoc, hX, inv_mul_cancel]
  have he : (t * exp (b : L))⁻¹ * X * (s * exp (a : L)) =
      exp (-(b : L)) * (t⁻¹ * X * s) * exp (a : L) := by
    rw [exp_neg]
    group
  apply Subtype.ext
  simp only [coe_logDefect, LieSubmodule.coe_sub, LieSubmodule.coe_add]
  rw [he, f.log_mul_of_mem_ker_bchGroupMap _ _ (f.bchGroupMap.ker.mul_mem hb hdef) ha,
    f.log_mul_of_mem_ker_bchGroupMap _ _ hb hdef, log_exp, log_exp]
  abel

/-- Around a closed triangle the logarithm of the ordered holonomy is the sum
of the three crossing defects. In particular this sum is independent of the lifts. -/
theorem log_triangle_eq_sum_logDefect (hc : f.ker ≤ LieAlgebra.center R L)
    (s t u X Y Z : BCHGroup L)
    (hX : f.bchGroupMap X * f.bchGroupMap s = f.bchGroupMap t)
    (hY : f.bchGroupMap Y * f.bchGroupMap t = f.bchGroupMap u)
    (hZ : f.bchGroupMap Z * f.bchGroupMap u = f.bchGroupMap s) :
    log (Z * (Y * X)) = (f.logDefect u s Z hZ : L) +
      (f.logDefect t u Y hY : L) + (f.logDefect s t X hX : L) := by
  have := LieAlgebra.abelian_of_le_center R L f.ker hc
  have hYX : f.bchGroupMap (Y * X) * f.bchGroupMap s = f.bchGroupMap u := by
    simp only [map_mul, mul_assoc, hX, hY]
  have hloop : Z * (Y * X) ∈ f.bchGroupMap.ker := by
    apply MonoidHom.mem_ker.mpr
    apply mul_right_cancel (b := f.bchGroupMap s)
    simp only [map_mul, one_mul, mul_assoc, hX, hY, hZ]
  have hconj : s⁻¹ * (Z * (Y * X)) * s = Z * (Y * X) := by
    have hcomm : Commute s⁻¹ (Z * (Y * X)) :=
      Subgroup.mem_center_iff.mp (f.ker_bchGroupMap_le_center hc hloop) s⁻¹
    simpa only [inv_inv] using hcomm.mul_inv_cancel
  have hsum := congrArg (fun a : f.ker => (a : L))
    (f.logDefect_mul s u s (Y * X) Z hYX hZ)
  rw [f.logDefect_mul s t u X Y hX hY] at hsum
  simpa only [LieSubmodule.coe_add, coe_logDefect, hconj, add_assoc] using hsum

end LieHom
