/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.LinearAlgebra.Basis.Diagonal
public import Mei.RingTheory.Node.NormalForm

/-!
# Gluing truncated chambers of a node

Let `t, f : R` with `t^(k+1) = 0`. The left and right chambers
`R[x,y]/(xy-t, y^(k+1))` and `R[x,y]/(xy-t, x^(k+1))` both map to the overlap
`R[x,y]/(xy-t, x^(k+1), y^(k+1))`. Inverting `f` on the overlap, glue the left chamber by
`x ↦ f x`, `y ↦ f⁻¹ y` and the right chamber by the identity. The fiber product of this cospan
is the *slab algebra*. If `f` is a nonzerodivisor modulo every power of `t`, then the slab
algebra is the nodal algebra `R[X,Y]/(XY - tf)`, by `X ↦ (x, f x)` and `Y ↦ (f y, y)`.

The proof compares monomial normal forms in `R[x,y]/(xy-t)`. The kernel `(y^(k+1))` of the
left chamber quotient has zero `x^n`-coordinates and `y^(d+1)`-coordinates divisible by
`t^(k-d)`. The kernel `(x^(k+1))` of the right chamber quotient has zero
`y^(d+1)`-coordinates and `x^n`-coordinates divisible by `t^(k+1-n)`.
The localized overlap is handled by clearing the denominators of the left gluing map.

For the focus-focus singularity, `R = S[w^{±1}]` with `S = K[t]/(t^(k+1))` and `f = 1 + w`;
the slab algebra is the coefficient algebra of the slab `u = 0`. This follows
Gross–Siebert, *An invitation to toric degenerations*, §2.3, arXiv:0808.2749v2, and
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
§3, arXiv:1601.07081v4.

## Main definitions

* `Mei.NodeAlgebra.slabAlgebra t f k`: the fiber product of the two chambers over the
  localized overlap.
* `Mei.NodeAlgebra.slabEquiv`: the isomorphism `R[X,Y]/(XY - tf) ≃ₐ[R] slabAlgebra t f k`.
-/

public section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra LaurentPolynomial Module

variable {R : Type*} [CommRing R]

section Truncation

variable (t : R) (k : ℕ)

private theorem leftLaurentMap_coord_zero_pow :
    leftLaurentMap t (coord t 0 ^ (k + 1)) = single ((k + 1 : ℕ) : ℤ) 1 := by
  simp [single_eq_C_mul_T]

private theorem leftLaurentMap_coord_one_pow :
    leftLaurentMap t (coord t 1 ^ (k + 1)) = single (-((k + 1 : ℕ) : ℤ)) (t ^ (k + 1)) := by
  simp [single_eq_C_mul_T, mul_pow]

private theorem rightLaurentMap_coord_zero_pow :
    rightLaurentMap t (coord t 0 ^ (k + 1)) = single (-((k + 1 : ℕ) : ℤ)) (t ^ (k + 1)) := by
  simp [single_eq_C_mul_T, mul_pow]

private theorem rightLaurentMap_coord_one_pow :
    rightLaurentMap t (coord t 1 ^ (k + 1)) = single ((k + 1 : ℕ) : ℤ) 1 := by
  simp [single_eq_C_mul_T]

private theorem span_coord_one_le :
    Ideal.span {coord t 1 ^ (k + 1)} ≤
      Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} :=
  Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))

private theorem span_coord_zero_le :
    Ideal.span {coord t 0 ^ (k + 1)} ≤
      Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} :=
  Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))

variable {t k}

/-- Coordinates of `X^n` in the ideal `(X^(k+1), Y^(k+1))` are divisible by `t^(k+1-n)`. -/
theorem pow_dvd_repr_inl_of_mem_span_pair {z : NodeAlgebra R t}
    (hz : z ∈ Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)}) (n : ℕ) :
    t ^ (k + 1 - n) ∣ (normalFormBasis t).repr z (.inl n) := by
  obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hz
  rw [normalFormBasis_repr_inl, map_add (leftLaurentMap t), map_mul, map_mul,
    leftLaurentMap_coord_zero_pow, leftLaurentMap_coord_one_pow, coeff_add, Finsupp.add_apply,
    coeff_mul_single_apply, coeff_mul_single_apply]
  refine dvd_add ?_ (Dvd.dvd.mul_left (pow_dvd_pow t (Nat.sub_le _ _)) _)
  rcases le_or_gt n k with hn | hn
  · have hi : (n : ℤ) + -((k + 1 : ℕ) : ℤ) = -(((k - n : ℕ) : ℤ) + 1) := by omega
    rw [hi, coeff_leftLaurentMap_neg_succ, mul_one, show k + 1 - n = k - n + 1 by omega]
    exact dvd_mul_right _ _
  · rw [show k + 1 - n = 0 by omega, pow_zero]
    exact one_dvd _

/-- Coordinates of `Y^(d+1)` in the ideal `(X^(k+1), Y^(k+1))` are divisible by `t^(k-d)`. -/
theorem pow_dvd_repr_inr_of_mem_span_pair {z : NodeAlgebra R t}
    (hz : z ∈ Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)}) (d : ℕ) :
    t ^ (k - d) ∣ (normalFormBasis t).repr z (.inr d) := by
  obtain ⟨c, e, rfl⟩ := Ideal.mem_span_pair.mp hz
  rw [normalFormBasis_repr_inr, map_add (rightLaurentMap t), map_mul, map_mul,
    rightLaurentMap_coord_zero_pow, rightLaurentMap_coord_one_pow, coeff_add, Finsupp.add_apply,
    coeff_mul_single_apply, coeff_mul_single_apply]
  refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow t (by omega)) _) ?_
  rcases le_or_gt k d with hd | hd
  · rw [show k - d = 0 by omega, pow_zero]
    exact one_dvd _
  · have hi : ((d + 1 : ℕ) : ℤ) + -((k + 1 : ℕ) : ℤ) = -((k - d : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_one] at hi
    rw [hi, coeff_rightLaurentMap_neg, mul_one]
    exact dvd_mul_right _ _

/-- Normal forms in `(Y^(k+1))`, when `t^(k+1) = 0`: no `X`-terms, and `t^(k-d)` divides the
coordinate of `Y^(d+1)`. -/
theorem mem_span_coord_one_pow_iff (ht : t ^ (k + 1) = 0) {z : NodeAlgebra R t} :
    z ∈ Ideal.span {coord t 1 ^ (k + 1)} ↔
      (∀ n, (normalFormBasis t).repr z (.inl n) = 0) ∧
        ∀ d, t ^ (k - d) ∣ (normalFormBasis t).repr z (.inr d) := by
  constructor
  · intro hz
    refine ⟨fun n => ?_, pow_dvd_repr_inr_of_mem_span_pair (span_coord_one_le t k hz)⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    simp [leftLaurentMap_coord_one_pow, ht]
  · rintro ⟨hl, hr⟩
    rw [← (normalFormBasis t).linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun i _ => ?_
    cases i with
    | inl n => simp [hl]
    | inr d =>
      obtain ⟨c, hc⟩ := hr d
      rw [hc, normalFormBasis_inr, Algebra.smul_def, map_mul, map_pow, ← coord_zero_mul_coord_one,
        mul_pow, Ideal.mem_span_singleton]
      have h : coord t 1 ^ (k + 1) ∣ coord t 1 ^ (k - d) * coord t 1 ^ (d + 1) := by
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      exact (h.mul_right (coord t 0 ^ (k - d) * algebraMap R _ c)).trans (dvd_of_eq (by ring))

/-- Normal forms in `(X^(k+1))`, when `t^(k+1) = 0`: no `Y`-terms, and `t^(k+1-n)` divides the
coordinate of `X^n`. -/
theorem mem_span_coord_zero_pow_iff (ht : t ^ (k + 1) = 0) {z : NodeAlgebra R t} :
    z ∈ Ideal.span {coord t 0 ^ (k + 1)} ↔
      (∀ d, (normalFormBasis t).repr z (.inr d) = 0) ∧
        ∀ n, t ^ (k + 1 - n) ∣ (normalFormBasis t).repr z (.inl n) := by
  constructor
  · intro hz
    refine ⟨fun d => ?_, pow_dvd_repr_inl_of_mem_span_pair (span_coord_zero_le t k hz)⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    simp [rightLaurentMap_coord_zero_pow, ht]
  · rintro ⟨hr, hl⟩
    rw [← (normalFormBasis t).linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun i _ => ?_
    cases i with
    | inl n =>
      obtain ⟨c, hc⟩ := hl n
      rw [hc, normalFormBasis_inl, Algebra.smul_def, map_mul, map_pow, ← coord_zero_mul_coord_one,
        mul_pow, Ideal.mem_span_singleton]
      have h : coord t 0 ^ (k + 1) ∣ coord t 0 ^ (k + 1 - n) * coord t 0 ^ n := by
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      exact (h.mul_right (coord t 1 ^ (k + 1 - n) * algebraMap R _ c)).trans (dvd_of_eq (by ring))
    | inr d => simp [hr]

end Truncation

noncomputable section Gluing

variable (t f : R) (k : ℕ)

/-- The left chamber `R[x,y]/(xy-t, y^(k+1))`. -/
abbrev LeftChamber := NodeAlgebra R t ⧸ Ideal.span {coord t 1 ^ (k + 1)}

/-- The right chamber `R[x,y]/(xy-t, x^(k+1))`. -/
abbrev RightChamber := NodeAlgebra R t ⧸ Ideal.span {coord t 0 ^ (k + 1)}

/-- The overlap `R[x,y]/(xy-t, x^(k+1), y^(k+1))` of the two chambers. -/
abbrev Overlap := NodeAlgebra R t ⧸ Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)}

/-- The overlap with the gluing function `f` inverted. -/
abbrev LocalizedOverlap := Localization.Away (algebraMap R (Overlap t k) f)

/-- The class of a coordinate in the localized overlap. -/
private def overlapCoord (i : Fin 2) : LocalizedOverlap t f k :=
  algebraMap (Overlap t k) _ (Ideal.Quotient.mk _ (coord t i))

private theorem overlapCoord_pow_succ (i : Fin 2) : overlapCoord t f k i ^ (k + 1) = 0 := by
  rw [overlapCoord, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
  fin_cases i <;> exact Ideal.subset_span (by simp)

private theorem overlapCoord_mul : overlapCoord t f k 0 * overlapCoord t f k 1 =
    algebraMap R (LocalizedOverlap t f k) t := by
  rw [overlapCoord, overlapCoord, ← map_mul, ← map_mul, coord_zero_mul_coord_one,
    Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The inverse of `f` in the localized overlap. -/
private abbrev fInv : LocalizedOverlap t f k :=
  IsLocalization.Away.invSelf (algebraMap R (Overlap t k) f)

private theorem algebraMap_mul_fInv : algebraMap R (LocalizedOverlap t f k) f * fInv t f k = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := LocalizedOverlap t f k)
    (algebraMap R (Overlap t k) f)
  rwa [← IsScalarTower.algebraMap_apply] at h

/-- The coordinate change `(x, y) ↦ (f x, f⁻¹ y)` into the localized overlap. -/
private def leftGluingLift : NodeAlgebra R t →ₐ[R] LocalizedOverlap t f k :=
  lift t (algebraMap R _ f * overlapCoord t f k 0) (fInv t f k * overlapCoord t f k 1) (by
    rw [mul_mul_mul_comm, algebraMap_mul_fInv, one_mul, overlapCoord_mul])

private theorem leftGluingLift_eq_zero :
    ∀ z ∈ Ideal.span {coord t 1 ^ (k + 1)}, leftGluingLift t f k z = 0 := fun z hz => by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [map_mul, map_pow, leftGluingLift, lift_coord_one, mul_pow, overlapCoord_pow_succ, mul_zero,
    mul_zero]

/-- The gluing map from the left chamber, `x ↦ f x` and `y ↦ f⁻¹ y`: the quotient map to the
overlap followed by the coordinate change `(x, y) ↦ (f x, f⁻¹ y)` of the localized overlap. -/
def leftGluing : LeftChamber t k →ₐ[R] LocalizedOverlap t f k :=
  Ideal.Quotient.liftₐ _ (leftGluingLift t f k) (leftGluingLift_eq_zero t f k)

private theorem leftGluing_mk (z : NodeAlgebra R t) :
    leftGluing t f k (Ideal.Quotient.mk _ z) = leftGluingLift t f k z :=
  AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp _ _ (leftGluingLift_eq_zero t f k)) z

/-- The gluing map from the right chamber: the quotient map to the overlap followed by
localization. -/
def rightGluing : RightChamber t k →ₐ[R] LocalizedOverlap t f k :=
  (IsScalarTower.toAlgHom R (Overlap t k) _).comp
    (Ideal.Quotient.factorₐ R (span_coord_zero_le t k))

/-- The left gluing map sends `x` to `f x`. -/
@[simp]
theorem leftGluing_mk_coord_zero :
    leftGluing t f k (Ideal.Quotient.mk _ (coord t 0)) =
      algebraMap R _ f * algebraMap (Overlap t k) _ (Ideal.Quotient.mk _ (coord t 0)) := by
  rw [leftGluing_mk, leftGluingLift, lift_coord_zero, overlapCoord]

/-- The left gluing map sends `y` to `f⁻¹ y`. -/
@[simp]
theorem leftGluing_mk_coord_one :
    leftGluing t f k (Ideal.Quotient.mk _ (coord t 1)) =
      IsLocalization.Away.invSelf (algebraMap R (Overlap t k) f) *
        algebraMap (Overlap t k) _ (Ideal.Quotient.mk _ (coord t 1)) := by
  rw [leftGluing_mk, leftGluingLift, lift_coord_one, overlapCoord]

/-- The right gluing map is the quotient map followed by localization. -/
@[simp]
theorem rightGluing_mk (z : NodeAlgebra R t) :
    rightGluing t f k (Ideal.Quotient.mk _ z) =
      algebraMap (Overlap t k) _ (Ideal.Quotient.mk _ z) := (rfl)

/-- The slab algebra: the fiber product of the two chambers over the localized overlap. -/
def slabAlgebra : Subalgebra R (LeftChamber t k × RightChamber t k) :=
  AlgHom.equalizer ((leftGluing t f k).comp (AlgHom.fst R _ _))
    ((rightGluing t f k).comp (AlgHom.snd R _ _))

/-- A pair lies in the slab algebra exactly when its two gluing images agree. -/
@[simp]
theorem mem_slabAlgebra_iff {p : LeftChamber t k × RightChamber t k} :
    p ∈ slabAlgebra t f k ↔ leftGluing t f k p.1 = rightGluing t f k p.2 := Iff.rfl

/-- The lift `x ↦ x`, `y ↦ f y` of the first slab coordinate. -/
private def scaleCoordOne : NodeAlgebra R (t * f) →ₐ[R] NodeAlgebra R t :=
  lift (t * f) (coord t 0) (algebraMap R _ f * coord t 1) (by
    rw [mul_left_comm, coord_zero_mul_coord_one, ← map_mul, mul_comm])

/-- The lift `x ↦ f x`, `y ↦ y` of the second slab coordinate. -/
private def scaleCoordZero : NodeAlgebra R (t * f) →ₐ[R] NodeAlgebra R t :=
  lift (t * f) (algebraMap R _ f * coord t 0) (coord t 1) (by
    rw [mul_assoc, coord_zero_mul_coord_one, ← map_mul, mul_comm])

private theorem scaleCoordOne_basis (i : ℕ ⊕ ℕ) :
    scaleCoordOne t f (normalFormBasis (t * f) i) =
      Sum.elim (fun _ => 1) (fun d => f ^ (d + 1)) i • normalFormBasis t i := by
  cases i <;> simp [scaleCoordOne, mul_pow, Algebra.smul_def]

private theorem scaleCoordZero_basis (i : ℕ ⊕ ℕ) :
    scaleCoordZero t f (normalFormBasis (t * f) i) =
      Sum.elim (fun n => f ^ n) (fun _ => 1) i • normalFormBasis t i := by
  cases i <;> simp [scaleCoordZero, mul_pow, Algebra.smul_def]

private theorem repr_scaleCoordOne (z : NodeAlgebra R (t * f)) (i : ℕ ⊕ ℕ) :
    (normalFormBasis t).repr (scaleCoordOne t f z) i =
      Sum.elim (fun _ => 1) (fun d => f ^ (d + 1)) i * (normalFormBasis (t * f)).repr z i :=
  Basis.repr_apply_of_apply_eq_smul _ _ (g := (scaleCoordOne t f).toLinearMap)
    (scaleCoordOne_basis t f) z i

private theorem repr_scaleCoordZero (z : NodeAlgebra R (t * f)) (i : ℕ ⊕ ℕ) :
    (normalFormBasis t).repr (scaleCoordZero t f z) i =
      Sum.elim (fun n => f ^ n) (fun _ => 1) i * (normalFormBasis (t * f)).repr z i :=
  Basis.repr_apply_of_apply_eq_smul _ _ (g := (scaleCoordZero t f).toLinearMap)
    (scaleCoordZero_basis t f) z i

private theorem leftGluing_comp_eq :
    (leftGluing t f k).comp ((Ideal.Quotient.mkₐ R _).comp (scaleCoordOne t f)) =
      (rightGluing t f k).comp ((Ideal.Quotient.mkₐ R _).comp (scaleCoordZero t f)) := by
  ext
  · simp [scaleCoordOne, scaleCoordZero]
  · simp only [AlgHom.comp_apply, scaleCoordOne, scaleCoordZero, lift_coord_one,
      Ideal.Quotient.mkₐ_eq_mk, map_mul, AlgHom.commutes,
      leftGluing_mk_coord_one, rightGluing_mk]
    rw [← mul_assoc, algebraMap_mul_fInv, one_mul]

/-- The comparison map `R[X,Y]/(XY - tf) → A`, `X ↦ (x, f x)`, `Y ↦ (f y, y)`. -/
def toSlabAlgebra : NodeAlgebra R (t * f) →ₐ[R] slabAlgebra t f k :=
  AlgHom.codRestrict (((Ideal.Quotient.mkₐ R _).comp (scaleCoordOne t f)).prod
    ((Ideal.Quotient.mkₐ R _).comp (scaleCoordZero t f))) _
    fun z => AlgHom.congr_fun (leftGluing_comp_eq t f k) z

/-- The comparison map sends `X` to `(x, f x)`. -/
@[simp]
theorem coe_toSlabAlgebra_coord_zero :
    (toSlabAlgebra t f k (coord (t * f) 0) : LeftChamber t k × RightChamber t k) =
      (Ideal.Quotient.mk _ (coord t 0),
        algebraMap R (RightChamber t k) f * Ideal.Quotient.mk _ (coord t 0)) := by
  simp [toSlabAlgebra, scaleCoordOne, scaleCoordZero]

/-- The comparison map sends `Y` to `(f y, y)`. -/
@[simp]
theorem coe_toSlabAlgebra_coord_one :
    (toSlabAlgebra t f k (coord (t * f) 1) : LeftChamber t k × RightChamber t k) =
      (algebraMap R (LeftChamber t k) f * Ideal.Quotient.mk _ (coord t 1),
        Ideal.Quotient.mk _ (coord t 1)) := by
  simp [toSlabAlgebra, scaleCoordOne, scaleCoordZero]

private theorem coe_toSlabAlgebra (z : NodeAlgebra R (t * f)) :
    (toSlabAlgebra t f k z : LeftChamber t k × RightChamber t k) =
      (Ideal.Quotient.mk _ (scaleCoordOne t f z), Ideal.Quotient.mk _ (scaleCoordZero t f z)) :=
  (rfl)

/-- Normal-form rescaling whose image in the localized overlap is `f^(k+1)` times the left
gluing map; it clears the denominators `f⁻¹` of `leftGluing`. -/
private def leftGluingNumerator : NodeAlgebra R t →ₗ[R] NodeAlgebra R t :=
  (normalFormBasis t).constr R fun i =>
    Sum.elim (fun n => f ^ (k + 1 + n)) (fun d => f ^ (k - d)) i • normalFormBasis t i

private theorem leftGluingNumerator_basis (i : ℕ ⊕ ℕ) :
    leftGluingNumerator t f k (normalFormBasis t i) =
      Sum.elim (fun n => f ^ (k + 1 + n)) (fun d => f ^ (k - d)) i • normalFormBasis t i :=
  (normalFormBasis t).constr_basis R _ i

private theorem repr_leftGluingNumerator (z : NodeAlgebra R t) (i : ℕ ⊕ ℕ) :
    (normalFormBasis t).repr (leftGluingNumerator t f k z) i =
      Sum.elim (fun n => f ^ (k + 1 + n)) (fun d => f ^ (k - d)) i *
        (normalFormBasis t).repr z i :=
  Basis.repr_apply_of_apply_eq_smul _ _ (leftGluingNumerator_basis t f k) z i

private theorem algebraMap_leftGluingNumerator (z : NodeAlgebra R t) :
    algebraMap (Overlap t k) (LocalizedOverlap t f k)
        (Ideal.Quotient.mk _ (leftGluingNumerator t f k z)) =
      algebraMap R _ f ^ (k + 1) * leftGluing t f k (Ideal.Quotient.mk _ z) := by
  have hY := overlapCoord_pow_succ t f k 1
  have hFG := algebraMap_mul_fInv t f k
  simp only [overlapCoord] at hY
  have h := (normalFormBasis t).ext
    (f₁ := ((IsScalarTower.toAlgHom R (Overlap t k) (LocalizedOverlap t f k)).comp
      (Ideal.Quotient.mkₐ R _)).toLinearMap ∘ₗ leftGluingNumerator t f k)
    (f₂ := f ^ (k + 1) • ((leftGluing t f k).comp (Ideal.Quotient.mkₐ R _)).toLinearMap)
    fun i => by
      rw [LinearMap.comp_apply, leftGluingNumerator_basis]
      cases i with
      | inl n =>
        simp only [Sum.elim_inl, normalFormBasis_inl, Algebra.smul_def, AlgHom.toLinearMap_apply,
          AlgHom.comp_apply, map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.mkₐ_eq_mk,
          LinearMap.smul_apply, IsScalarTower.coe_toAlgHom', leftGluing_mk_coord_zero, mul_pow]
        ring
      | inr d =>
        simp only [Sum.elim_inr, normalFormBasis_inr, Algebra.smul_def, AlgHom.toLinearMap_apply,
          AlgHom.comp_apply, map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.mkₐ_eq_mk,
          LinearMap.smul_apply, IsScalarTower.coe_toAlgHom', leftGluing_mk_coord_one, mul_pow]
        rcases le_or_gt d k with hd | hd
        · have hk : algebraMap R (LocalizedOverlap t f k) f ^ (k + 1) =
              algebraMap R _ f ^ (k - d) * algebraMap R _ f ^ (d + 1) := by
            rw [← pow_add]
            congr 1
            omega
          have hFG' : (algebraMap R (LocalizedOverlap t f k) f * fInv t f k) ^ (d + 1) = 1 := by
            rw [hFG, one_pow]
          rw [hk]
          linear_combination (-(algebraMap R (LocalizedOverlap t f k) f ^ (k - d) *
            algebraMap (Overlap t k) _ (Ideal.Quotient.mk _ (coord t 1)) ^ (d + 1))) * hFG'
        · have hd' : algebraMap (Overlap t k) (LocalizedOverlap t f k)
              (Ideal.Quotient.mk _ (coord t 1)) ^ (d + 1) = 0 := by
            rw [show d + 1 = (k + 1) + (d - k) by omega, pow_add, hY, zero_mul]
          simp [hd']
  simpa [Algebra.smul_def] using LinearMap.congr_fun h z

variable {t k}

/-- The comparison map is injective when `t^(k+1) = 0`: the `X`-coordinates are read in the
left chamber and the `Y`-coordinates in the right chamber. -/
theorem toSlabAlgebra_injective (ht : t ^ (k + 1) = 0) :
    Function.Injective (toSlabAlgebra t f k) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  have h₁ : scaleCoordOne t f z ∈ Ideal.span {coord t 1 ^ (k + 1)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [coe_toSlabAlgebra, ZeroMemClass.coe_zero, Prod.fst_zero] using
        congrArg (fun p : slabAlgebra t f k => (p : LeftChamber t k × RightChamber t k).1) hz)
  have h₂ : scaleCoordZero t f z ∈ Ideal.span {coord t 0 ^ (k + 1)} :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [coe_toSlabAlgebra, ZeroMemClass.coe_zero, Prod.snd_zero] using
        congrArg (fun p : slabAlgebra t f k => (p : LeftChamber t k × RightChamber t k).2) hz)
  apply (normalFormBasis (t * f)).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  cases i with
  | inl n =>
    have h := ((mem_span_coord_one_pow_iff ht).mp h₁).1 n
    rwa [repr_scaleCoordOne, Sum.elim_inl, one_mul] at h
  | inr d =>
    have h := ((mem_span_coord_zero_pow_iff ht).mp h₂).1 d
    rwa [repr_scaleCoordZero, Sum.elim_inr, one_mul] at h

/-- The comparison map is surjective when `t^(k+1) = 0` and `f` is a nonzerodivisor modulo
every power of `t`. -/
theorem toSlabAlgebra_surjective (ht : t ^ (k + 1) = 0)
    (hf : ∀ (j : ℕ) (c : R), t ^ j ∣ f * c → t ^ j ∣ c) :
    Function.Surjective (toSlabAlgebra t f k) := by
  rintro ⟨⟨r, s⟩, hrs⟩
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hfpow (m j : ℕ) (c : R) (h : t ^ j ∣ f ^ m * c) : t ^ j ∣ c := by
    induction m with
    | zero => simpa using h
    | succ m ih => exact ih (hf j _ (by rwa [pow_succ', mul_assoc] at h))
  -- the gluing condition, after clearing denominators, holds up to a power of `f`
  have hw : algebraMap (Overlap t k) (LocalizedOverlap t f k)
      (Ideal.Quotient.mk _ (leftGluingNumerator t f k u - f ^ (k + 1) • v)) = 0 := by
    rw [mem_slabAlgebra_iff] at hrs
    rw [map_sub, map_sub, algebraMap_leftGluingNumerator, hrs, rightGluing_mk, Algebra.smul_def,
      map_mul, map_mul, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply, map_pow,
      sub_self]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap R (Overlap t k) f)) _ _).mp hw
  have hmem : f ^ m • (leftGluingNumerator t f k u - f ^ (k + 1) • v) ∈
      Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap,
      map_pow]
    exact hm
  have hrepr (i : ℕ ⊕ ℕ) : (normalFormBasis t).repr
      (f ^ m • (leftGluingNumerator t f k u - f ^ (k + 1) • v)) i =
        f ^ m * (Sum.elim (fun n => f ^ (k + 1 + n)) (fun d => f ^ (k - d)) i *
          (normalFormBasis t).repr u i - f ^ (k + 1) * (normalFormBasis t).repr v i) := by
    rw [map_smul, map_sub, map_smul, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      repr_leftGluingNumerator, smul_eq_mul, smul_eq_mul]
  have hX (n : ℕ) : t ^ (k + 1 - n) ∣
      f ^ n * (normalFormBasis t).repr u (.inl n) - (normalFormBasis t).repr v (.inl n) := by
    have h := pow_dvd_repr_inl_of_mem_span_pair hmem n
    rw [hrepr, Sum.elim_inl] at h
    exact hfpow (m + (k + 1)) _ _ (h.trans (dvd_of_eq (by ring)))
  have hY (d : ℕ) : t ^ (k - d) ∣
      (normalFormBasis t).repr u (.inr d) - f ^ (d + 1) * (normalFormBasis t).repr v (.inr d) := by
    rcases le_or_gt d k with hd | hd
    · have h := pow_dvd_repr_inr_of_mem_span_pair hmem d
      rw [hrepr, Sum.elim_inr, show k + 1 = (k - d) + (d + 1) by omega, pow_add] at h
      exact hfpow (m + (k - d)) _ _ (h.trans (dvd_of_eq (by ring)))
    · rw [show k - d = 0 by omega, pow_zero]
      exact one_dvd _
  -- the preimage takes its `X`-coordinates from `u` and its `Y`-coordinates from `v`
  let p := (normalFormBasis (t * f)).repr.symm
    (Finsupp.sumElim ((normalFormBasis t).repr u |>.comapDomain Sum.inl Sum.inl_injective.injOn)
      ((normalFormBasis t).repr v |>.comapDomain Sum.inr Sum.inr_injective.injOn))
  have hpl (n : ℕ) : (normalFormBasis (t * f)).repr p (.inl n) =
      (normalFormBasis t).repr u (.inl n) := by
    rw [LinearEquiv.apply_symm_apply, Finsupp.sumElim_inl, Finsupp.comapDomain_apply]
  have hpr (d : ℕ) : (normalFormBasis (t * f)).repr p (.inr d) =
      (normalFormBasis t).repr v (.inr d) := by
    rw [LinearEquiv.apply_symm_apply, Finsupp.sumElim_inr, Finsupp.comapDomain_apply]
  refine ⟨p, Subtype.ext (Prod.ext ?_ ?_)⟩
  · rw [coe_toSlabAlgebra, Ideal.Quotient.eq, mem_span_coord_one_pow_iff ht]
    refine ⟨fun n => ?_, fun d => ?_⟩
    · rw [map_sub, Finsupp.sub_apply, repr_scaleCoordOne, Sum.elim_inl, one_mul, hpl, sub_self]
    · rw [map_sub, Finsupp.sub_apply, repr_scaleCoordOne, Sum.elim_inr, hpr, ← dvd_neg, neg_sub]
      exact hY d
  · rw [coe_toSlabAlgebra, Ideal.Quotient.eq, mem_span_coord_zero_pow_iff ht]
    refine ⟨fun d => ?_, fun n => ?_⟩
    · rw [map_sub, Finsupp.sub_apply, repr_scaleCoordZero, Sum.elim_inr, one_mul, hpr, sub_self]
    · rw [map_sub, Finsupp.sub_apply, repr_scaleCoordZero, Sum.elim_inl, hpl]
      exact hX n

/-- **The slab algebra of a node.** If `t^(k+1) = 0` and `f` is a nonzerodivisor modulo every
power of `t`, the fiber product of the truncated chambers glued by `x ↦ f x`, `y ↦ f⁻¹ y` is
`R[X,Y]/(XY - tf)`, with `X = (x, f x)` and `Y = (f y, y)`. -/
def slabEquiv (ht : t ^ (k + 1) = 0) (hf : ∀ (j : ℕ) (c : R), t ^ j ∣ f * c → t ^ j ∣ c) :
    NodeAlgebra R (t * f) ≃ₐ[R] slabAlgebra t f k :=
  AlgEquiv.ofBijective (toSlabAlgebra t f k)
    ⟨toSlabAlgebra_injective f ht, toSlabAlgebra_surjective f ht hf⟩

/-- `slabEquiv` is the comparison map `toSlabAlgebra`. -/
@[simp]
theorem slabEquiv_apply (ht : t ^ (k + 1) = 0)
    (hf : ∀ (j : ℕ) (c : R), t ^ j ∣ f * c → t ^ j ∣ c) (z : NodeAlgebra R (t * f)) :
    slabEquiv f ht hf z = toSlabAlgebra t f k z := (rfl)

end Gluing


end Mei.NodeAlgebra
