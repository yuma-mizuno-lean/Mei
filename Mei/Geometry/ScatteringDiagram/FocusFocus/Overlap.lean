/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Overlap
public import Mei.RingTheory.Node.SlabMap
public import Mei.Algebra.Polynomial.Laurent

/-!
# The two gluing descriptions of the focus-focus overlap

On the truncated nodal overlap over `S[w,w⁻¹]`, the upper chart change is
`(x,y,w) ↦ (wx,w⁻¹y,w)`. In the localization at `f = 1+w`, gluing with
`f' = 1+w⁻¹` after that chart change equals gluing with `f` directly.
We construct both maps on the actual overlap quotient and identify their
composite from the left chamber with the existing `NodeAlgebra.leftGluing`.
Thus the fiber-product slab algebra has the same left incidence map in either
chart description. The upper chart transition commutes with coefficient change
and reduction of the cutoff. No nilpotence assumption on the coefficient `t` is needed.

The coordinate changes follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4). We use `NodeAlgebra.overlapRescale` for the quotient maps.
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti TauCeti.NodeAlgebra _root_.LaurentPolynomial Mei.NodeAlgebra

variable {S : Type*} [CommRing S] (t : S) (k : ℕ)

local notation "R" => S[T;T⁻¹]
local notation "O" => Overlap (C t) k
local notation "D" => LocalizedOverlap (C t) (1 + T 1) k

private def fUnit : Dˣ :=
  Units.mkOfMulEqOne (algebraMap R D (1 + T 1))
    (IsLocalization.Away.invSelf (algebraMap R O (1 + T 1))) (by
      rw [IsScalarTower.algebraMap_apply R O D]
      exact IsLocalization.Away.mul_invSelf _)

private theorem fUnit_val : (fUnit t k : Dˣ).val = algebraMap R D (1 + T 1) := (rfl)

private theorem fUnit_inv_val : (↑(fUnit t k)⁻¹ : D) =
    IsLocalization.Away.invSelf (algebraMap R O (1 + T 1)) := (rfl)

/-- The upper chart transition on the truncated overlap: `x ↦ wx`, `y ↦ w⁻¹y`.
It fixes the tangential coefficient algebra and has the inverse rescaling. -/
def upperOverlap : O ≃ₐ[R] O :=
  overlapRescaleEquiv (C t) k (unitOfInvertible (T 1 : R))

/-- The upper chart multiplies the first coordinate by `w`. -/
@[simp]
theorem upperOverlap_coord_zero :
    upperOverlap t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R O (T 1) * Ideal.Quotient.mk _ (coord (C t) 0) := by
  simp [upperOverlap, unitOfInvertible]

/-- The upper chart multiplies the second coordinate by `w⁻¹`. -/
@[simp]
theorem upperOverlap_coord_one :
    upperOverlap t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      algebraMap R O (T (-1)) * Ideal.Quotient.mk _ (coord (C t) 1) := by
  simp [upperOverlap, unitOfInvertible, Units.inv_mk, invOf_T]

/-- Lower-overlap gluing, `x ↦ (1+w)x`, `y ↦ (1+w)⁻¹y`. -/
def lowerOverlapGluing : O →ₐ[R] D := overlapRescale (C t) k (fUnit t k)

/-- Upper-overlap gluing, `x ↦ (1+w⁻¹)x`, `y ↦ (1+w⁻¹)⁻¹y`,
in the same localization as the lower-overlap map. -/
def upperOverlapGluing : O →ₐ[R] D :=
  overlapRescale (C t) k
    (Units.map (algebraMap R D) (unitOfInvertible (T 1 : R))⁻¹ * fUnit t k)

/-- The lower gluing map has multiplier `1+w` on the first coordinate. -/
@[simp]
theorem lowerOverlapGluing_coord_zero :
    lowerOverlapGluing t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R D (1 + T 1) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 0)) := by
  simp [lowerOverlapGluing, fUnit_val]

/-- The lower gluing map uses the localization inverse on the second coordinate. -/
@[simp]
theorem lowerOverlapGluing_coord_one :
    lowerOverlapGluing t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      IsLocalization.Away.invSelf (algebraMap R O (1 + T 1)) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 1)) := by
  simp [lowerOverlapGluing, fUnit_inv_val]

/-- The upper multiplier is `1+w⁻¹`, since `w⁻¹(1+w)=1+w⁻¹`. -/
@[simp]
theorem upperOverlapGluing_coord_zero :
    upperOverlapGluing t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R D (1 + T (-1)) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 0)) := by
  have hw : (T (-1) : R) * (1 + T 1) = 1 + T (-1) := by
    rw [mul_add, mul_one, ← T_add]
    norm_num [add_comm]
  simp only [upperOverlapGluing, overlapRescale_coord_zero, Units.val_mul,
    Units.coe_map, unitOfInvertible, Units.inv_mk, invOf_T, fUnit_val]
  congr 1
  exact (map_mul (algebraMap R D) _ _).symm.trans (congrArg (algebraMap R D) hw)

/-- The inverse upper multiplier is `w(1+w)⁻¹`; no second localization is required. -/
@[simp]
theorem upperOverlapGluing_coord_one :
    upperOverlapGluing t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      (algebraMap R D (T 1) *
        IsLocalization.Away.invSelf (algebraMap R O (1 + T 1))) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 1)) := by
  simp only [upperOverlapGluing, overlapRescale_coord_one, mul_inv_rev, Units.val_mul,
    ← map_inv, inv_inv, Units.coe_map, unitOfInvertible, fUnit_inv_val]
  congr 1
  exact mul_comm _ _

/-- The upper chart transition followed by upper gluing equals lower gluing
on every element of the overlap quotient. -/
theorem upperOverlapGluing_comp_upperOverlap :
    (upperOverlapGluing t k).comp (upperOverlap t k).toAlgHom = lowerOverlapGluing t k := by
  rw [upperOverlap, overlapRescaleEquiv_toAlgHom, upperOverlapGluing,
    overlapRescale_comp]
  rw [map_inv, mul_inv_cancel_left]
  rfl

/-- The lower description recovers the existing left chamber incidence map. -/
theorem lowerOverlapGluing_comp_leftToOverlap :
    (lowerOverlapGluing t k).comp (leftToOverlap (C t) k) =
      leftGluing (C t) (1 + T 1) k := by
  apply Ideal.Quotient.algHom_ext
  apply TauCeti.NodeAlgebra.hom_ext
  · simp
  · simp

section Compatibility

open scoped AlgebraMonoidAlgebra

variable {S' : Type*} [CommRing S'] [Algebra S S'] {t' : S'}
  (ht : algebraMap S S' t = t') {k' : ℕ} (hk : k' ≤ k)

/-- Coefficient change and reduction to a smaller cutoff commute with the upper
chart transition. This includes the reduction squares of the overlap tower. -/
theorem overlapMap_upperOverlap (z : O) :
    overlapMap (C t)
        ((Mei.LaurentPolynomial.algebraMap_C t).trans (congrArg C ht)) hk
        (upperOverlap t k z) =
      upperOverlap t' k'
        (overlapMap (C t)
          ((Mei.LaurentPolynomial.algebraMap_C t).trans (congrArg C ht)) hk z) := by
  have h : (overlapMap (C t)
        ((Mei.LaurentPolynomial.algebraMap_C t).trans (congrArg C ht)) hk).comp
        (upperOverlap t k).toAlgHom =
      ((upperOverlap t' k').toAlgHom.restrictScalars R).comp
        (overlapMap (C t)
          ((Mei.LaurentPolynomial.algebraMap_C t).trans (congrArg C ht)) hk) := by
    apply overlap_hom_ext <;>
      simp [IsScalarTower.algebraMap_apply R S'[T;T⁻¹],
        T, -single_eq_C_mul_T]
  exact AlgHom.congr_fun h z

end Compatibility

end Mei.FocusFocus
