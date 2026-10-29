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
# The two focus-focus overlap descriptions

On the truncated nodal overlap over `S[w,w⁻¹]`, the upper chart transition sends
`x ↦ wx`, `y ↦ w⁻¹y`. The lower wall function is `f = 1+w`; the upper wall
function is `f' = 1+w⁻¹`. Both become units in the same localization at `f`,
since `f = wf'`. We construct the two wall maps and prove that composing the
upper wall map with the upper chart transition gives the lower wall map.
Thus the two descriptions give the same coefficient identifications, including
over rings with nilpotents or zero divisors. The upper chart transition also
commutes with coefficient change and reduction of the cutoff, and the lower
wall map factors the left chamber incidence through its overlap quotient.

We use `NodeAlgebra.twistOverlap` and its scalar composition law. The coordinates
and overlap identity follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3, arXiv:0808.2749v2, and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3, arXiv:1601.07081v4.
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti TauCeti.NodeAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial

variable {S : Type*} [CommRing S] (t : S) (k : ℕ)

local notation "R" => S[T;T⁻¹]
local notation "O" => Overlap (C t) k
local notation "D" => LocalizedOverlap (C t) (1 + T 1) k

private def wUnit : Rˣ :=
  unitOfInvertible (T 1 : R)

/-- The upper overlap identification `(x,y,w) ↦ (wx,w⁻¹y,w)`. -/
def upperOverlap : O ≃ₐ[R] O := scaleOverlap (C t) k (wUnit (S := S))

/-- The upper identification multiplies `x` by `w`. -/
@[simp]
theorem upperOverlap_mk_coord_zero :
    upperOverlap t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R O (T 1) * Ideal.Quotient.mk _ (coord (C t) 0) := by
  simp [upperOverlap, wUnit]

/-- The upper identification multiplies `y` by `w⁻¹`. -/
@[simp]
theorem upperOverlap_mk_coord_one :
    upperOverlap t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      algebraMap R O (T (-1)) * Ideal.Quotient.mk _ (coord (C t) 1) := by
  simp [upperOverlap, wUnit]

/-- The lower wall function as a unit of the common localized overlap. -/
def slabFunctionUnit : Dˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := D)
    (algebraMap R O (1 + T 1))).unit

/-- The lower wall unit has value `1+w`. -/
@[simp]
theorem coe_slabFunctionUnit :
    (slabFunctionUnit t k : D) = algebraMap R D (1 + T 1) := by
  rw [slabFunctionUnit, IsUnit.unit_spec, ← IsScalarTower.algebraMap_apply]

/-- The inverse lower wall unit is the canonical localization inverse. -/
@[simp]
theorem coe_inv_slabFunctionUnit :
    (↑(slabFunctionUnit t k)⁻¹ : D) =
      IsLocalization.Away.invSelf (algebraMap R O (1 + T 1)) := by
  apply inv_unique (x := algebraMap R D (1 + T 1))
  · rw [← coe_slabFunctionUnit, Units.mul_inv]
  · simpa only [IsScalarTower.algebraMap_apply R O D] using
      IsLocalization.Away.mul_invSelf (S := D) (algebraMap R O (1 + T 1))

/-- The upper wall function is a unit in the same localization, since it is
`w⁻¹(1+w)`. -/
def upperSlabFunctionUnit : Dˣ :=
  Units.map (algebraMap R D).toMonoidHom (wUnit (S := S))⁻¹ * slabFunctionUnit t k

/-- The upper wall unit has value `1+w⁻¹`. -/
@[simp]
theorem coe_upperSlabFunctionUnit :
    (upperSlabFunctionUnit t k : D) = algebraMap R D (1 + T (-1)) := by
  simp only [upperSlabFunctionUnit, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    coe_slabFunctionUnit]
  rw [← map_mul]
  simp only [wUnit, unitOfInvertible, Units.inv_mk, Units.val_mk, invOf_T,
    mul_add, mul_one, ← T_add]
  simp only [Int.reduceAdd, T_zero, add_comm]

/-- The inverse upper wall unit is `w(1+w)⁻¹` in the common localization. -/
@[simp]
theorem coe_inv_upperSlabFunctionUnit :
    (↑(upperSlabFunctionUnit t k)⁻¹ : D) =
      algebraMap R D (T 1) *
        IsLocalization.Away.invSelf (algebraMap R O (1 + T 1)) := by
  simp only [upperSlabFunctionUnit, mul_inv_rev, Units.val_mul, ← map_inv,
    inv_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    wUnit, unitOfInvertible, coe_inv_slabFunctionUnit]
  exact mul_comm _ _

/-- The lower wall map `x ↦ fx`, `y ↦ f⁻¹y` after the identity overlap identification. -/
def lowerWallMap : O →ₐ[R] D :=
  twistOverlap (C t) k (IsScalarTower.toAlgHom R O D) (slabFunctionUnit t k)

/-- The upper wall map `x ↦ f'x`, `y ↦ (f')⁻¹y`, with values in the common localization. -/
def upperWallMap : O →ₐ[R] D :=
  twistOverlap (C t) k (IsScalarTower.toAlgHom R O D) (upperSlabFunctionUnit t k)

/-- The lower wall multiplies `x` by `1+w`. -/
@[simp]
theorem lowerWallMap_mk_coord_zero :
    lowerWallMap t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R D (1 + T 1) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 0)) := by
  simp [lowerWallMap]

/-- The lower wall multiplies `y` by the inverse of `1+w`. -/
@[simp]
theorem lowerWallMap_mk_coord_one :
    lowerWallMap t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      IsLocalization.Away.invSelf (algebraMap R O (1 + T 1)) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 1)) := by
  simp [lowerWallMap]

/-- The upper wall multiplies `x` by `1+w⁻¹`. -/
@[simp]
theorem upperWallMap_mk_coord_zero :
    upperWallMap t k (Ideal.Quotient.mk _ (coord (C t) 0)) =
      algebraMap R D (1 + T (-1)) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 0)) := by
  simp [upperWallMap]

/-- The upper wall multiplies `y` by the inverse upper wall unit. -/
@[simp]
theorem upperWallMap_mk_coord_one :
    upperWallMap t k (Ideal.Quotient.mk _ (coord (C t) 1)) =
      (↑((upperSlabFunctionUnit t k)⁻¹) : D) *
        algebraMap O D (Ideal.Quotient.mk _ (coord (C t) 1)) := by
  simp [upperWallMap]

/-- On nodal representatives the lower overlap map is the existing slab gluing
map from the left chamber. -/
theorem lowerWallMap_mk (z : NodeAlgebra R (C t)) :
    lowerWallMap t k (Ideal.Quotient.mk _ z) =
      leftGluing (C t) (1 + T 1) k (Ideal.Quotient.mk _ z) := by
  have h : (lowerWallMap t k).comp (Ideal.Quotient.mkₐ R _) =
      (leftGluing (C t) (1 + T 1) k).comp (Ideal.Quotient.mkₐ R _) := by
    ext <;> simp
  exact AlgHom.congr_fun h z

/-- The two focus-focus crossing descriptions agree on every truncated overlap
element: `g_f ∘ h_II = g_f' ∘ h_III`. -/
theorem lowerWallMap_eq_upperWallMap_comp_upperOverlap :
    lowerWallMap t k = (upperWallMap t k).comp (upperOverlap t k).toAlgHom := by
  rw [upperWallMap, upperOverlap, scaleOverlap_toAlgHom, twistOverlap_comp]
  unfold lowerWallMap
  congr 1
  rw [upperSlabFunctionUnit, mul_right_comm, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- The lower description recovers the existing left chamber incidence map. -/
theorem lowerWallMap_comp_leftToOverlap :
    (lowerWallMap t k).comp (leftToOverlap (C t) k) =
      leftGluing (C t) (1 + T 1) k := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro z
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, leftToOverlap_mk] using
    lowerWallMap_mk t k z

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
