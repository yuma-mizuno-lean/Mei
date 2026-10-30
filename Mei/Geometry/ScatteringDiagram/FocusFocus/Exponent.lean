/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Data.Fin.VecNotation

/-!
# Exponents of the focus-focus chambers

The exponent monoid consists of triples `(a,b,h)` with `h ≥ 0` and `h-a ≥ 0`.
Its free coordinates are the Laurent exponent `b`, the multiplicity `h` of `y`,
and the multiplicity `h-a` of `x`. Thus `xy=t`, while the left and right chamber
orders count the `y` and `x` factors respectively. We identify order cutoffs with
translates by powers of these generators.

The upper chart change shears the vertical exponent by the horizontal exponent.
It preserves the monoid and both chamber orders and intertwines projection to
the tangent lattice. These are the exponent data behind the two chamber
presentations and their monomial truncations.

The shears use Mathlib’s `LinearEquiv.skewProd`; monomial ideal membership
uses `AddMonoidAlgebra.mem_ideal_span_of'_image`.
The coordinates follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public section

namespace Mei.FocusFocus

/-- The focus-focus exponent monoid; the middle coordinate is unrestricted. -/
def exponentMonoid : AddSubmonoid (ℤ × ℤ × ℤ) where
  carrier := {q | 0 ≤ q.2.2 ∧ 0 ≤ q.2.2 - q.1}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega

@[simp]
theorem mem_exponentMonoid (q : ℤ × ℤ × ℤ) :
    q ∈ exponentMonoid ↔ 0 ≤ q.2.2 ∧ 0 ≤ q.2.2 - q.1 := Iff.rfl

/-- Free additive coordinates `(b, y-multiplicity, x-multiplicity)` on the
exponent monoid. In particular, the two nonnegative coordinates are independent. -/
def exponentEquiv : exponentMonoid ≃+ ℤ × ℕ × ℕ where
  toFun q := (q.val.2.1, q.val.2.2.toNat, (q.val.2.2 - q.val.1).toNat)
  invFun q := ⟨((q.2.1 : ℤ) - q.2.2, q.1, q.2.1), by simp⟩
  left_inv q := by
    apply Subtype.ext
    have hq := q.property
    simp only [mem_exponentMonoid] at hq
    apply Prod.ext
    · dsimp
      omega
    · apply Prod.ext <;> dsimp
      omega
  right_inv q := by
    rcases q with ⟨b, r, s⟩
    simp
  map_add' q r := by
    have hq := q.property
    have hr := r.property
    simp only [mem_exponentMonoid] at hq hr
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> dsimp
      all_goals omega

/-- The free coordinates are the vertical exponent and the two chamber orders. -/
@[simp]
theorem exponentEquiv_apply (q : exponentMonoid) :
    exponentEquiv q = (q.val.2.1, q.val.2.2.toNat, (q.val.2.2 - q.val.1).toNat) := (rfl)

/-- Recover the exponent from its Laurent coordinate and generator multiplicities. -/
@[simp]
theorem coe_exponentEquiv_symm (q : ℤ × ℕ × ℕ) :
    (exponentEquiv.symm q).val = ((q.2.1 : ℤ) - q.2.2, q.1, (q.2.1 : ℤ)) := (rfl)

/-- The exponent of `x`. -/
def xDegree : exponentMonoid := ⟨(-1, 0, 0), by simp⟩

/-- The exponent of `y`. -/
def yDegree : exponentMonoid := ⟨(1, 0, 1), by simp⟩

/-- The exponent of the smoothing parameter `t`. -/
def smoothingDegree : exponentMonoid := ⟨(0, 0, 1), by simp⟩

/-- Laurent powers of the tangential variable `w` have order zero on both sides. -/
def tangentDegree : ℤ →+ exponentMonoid where
  toFun b := ⟨(0, b, 0), by simp⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_xDegree : xDegree.val = (-1, 0, 0) := (rfl)
@[simp] theorem coe_yDegree : yDegree.val = (1, 0, 1) := (rfl)
@[simp] theorem coe_smoothingDegree : smoothingDegree.val = (0, 0, 1) := (rfl)
@[simp] theorem coe_tangentDegree (b : ℤ) : (tangentDegree b).val = (0, b, 0) := (rfl)

/-- The monomial relation `xy=t` holds already in the exponent lattice. -/
theorem xDegree_add_yDegree : xDegree + yDegree = smoothingDegree := (rfl)

/-- The inverse free-coordinate map reconstructs the monomial from its Laurent
coordinate and nonnegative `y` and `x` multiplicities. -/
theorem exponentEquiv_symm_eq (c : ℤ × ℕ × ℕ) :
    exponentEquiv.symm c = tangentDegree c.1 + c.2.1 • yDegree + c.2.2 • xDegree := by
  apply exponentEquiv.injective
  simp only [AddEquiv.apply_symm_apply, map_add, map_nsmul,
    exponentEquiv_apply, coe_tangentDegree, coe_yDegree, coe_xDegree]
  ext <;> simp

/-- Left chamber order counts `y` factors. -/
def leftOrder : exponentMonoid →+ ℕ :=
  (AddMonoidHom.fst ℕ ℕ).comp ((AddMonoidHom.snd ℤ (ℕ × ℕ)).comp
    exponentEquiv.toAddMonoidHom)

/-- Right chamber order counts `x` factors. -/
def rightOrder : exponentMonoid →+ ℕ :=
  (AddMonoidHom.snd ℕ ℕ).comp ((AddMonoidHom.snd ℤ (ℕ × ℕ)).comp
    exponentEquiv.toAddMonoidHom)

/-- The order used for the right (`i=0`) or left (`i=1`) chamber cutoff. -/
def chamberOrder (i : Fin 2) : exponentMonoid →+ ℕ := ![rightOrder, leftOrder] i

@[simp] theorem chamberOrder_zero : chamberOrder 0 = rightOrder := (rfl)
@[simp] theorem chamberOrder_one : chamberOrder 1 = leftOrder := (rfl)

@[simp] theorem leftOrder_apply (q : exponentMonoid) : leftOrder q = q.val.2.2.toNat := (rfl)
@[simp] theorem rightOrder_apply (q : exponentMonoid) :
    rightOrder q = (q.val.2.2 - q.val.1).toNat := (rfl)

/-- Left order is the original integral coordinate `h`. -/
theorem natCast_leftOrder (q : exponentMonoid) :
    (leftOrder q : ℤ) = q.val.2.2 := Int.toNat_of_nonneg q.property.1

/-- Right order is the original integral coordinate `h-a`. -/
theorem natCast_rightOrder (q : exponentMonoid) :
    (rightOrder q : ℤ) = q.val.2.2 - q.val.1 := Int.toNat_of_nonneg q.property.2

/-- For a nonpositive horizontal exponent, the right order is the left order
plus its absolute value. -/
theorem rightOrder_eq_leftOrder_add_natAbs (q : exponentMonoid) (hq : q.val.1 ≤ 0) :
    rightOrder q = leftOrder q + q.val.1.natAbs := by
  have := natCast_leftOrder q
  have := natCast_rightOrder q
  have := Int.natAbs_of_nonneg (neg_nonneg.mpr hq)
  rw [Int.natAbs_neg] at this
  omega

/-- For a nonnegative horizontal exponent, the left order is the right order
plus its absolute value. -/
theorem leftOrder_eq_rightOrder_add_natAbs (q : exponentMonoid) (hq : 0 ≤ q.val.1) :
    leftOrder q = rightOrder q + q.val.1.natAbs := by
  have := natCast_leftOrder q
  have := natCast_rightOrder q
  have := Int.natAbs_of_nonneg hq
  omega

/-- The left order cutoff is exactly divisibility by the corresponding power of `y`. -/
theorem le_leftOrder_iff (q : exponentMonoid) (k : ℕ) :
    k ≤ leftOrder q ↔ ∃ r : exponentMonoid, q = k • yDegree + r := by
  constructor
  · intro hk
    refine ⟨exponentEquiv.symm (q.val.2.1, leftOrder q - k, rightOrder q), ?_⟩
    apply exponentEquiv.injective
    rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]
    simp only [leftOrder_apply] at hk
    ext <;> simp; omega
  · rintro ⟨r, rfl⟩
    rw [map_add, map_nsmul]
    have hy : leftOrder yDegree = 1 := (rfl)
    simp [hy]

/-- The right order cutoff is exactly divisibility by the corresponding power of `x`. -/
theorem le_rightOrder_iff (q : exponentMonoid) (k : ℕ) :
    k ≤ rightOrder q ↔ ∃ r : exponentMonoid, q = k • xDegree + r := by
  constructor
  · intro hk
    refine ⟨exponentEquiv.symm (q.val.2.1, leftOrder q, rightOrder q - k), ?_⟩
    apply exponentEquiv.injective
    rw [map_add, map_nsmul, AddEquiv.apply_symm_apply]
    simp only [rightOrder_apply] at hk
    ext <;> simp; omega
  · rintro ⟨r, rfl⟩
    rw [map_add, map_nsmul]
    have hx : rightOrder xDegree = 1 := (rfl)
    simp [hx]

/-- The quotient by `y^k` deletes exactly the monomials of left order at least `k`.
This holds over arbitrary semirings, including those with zero divisors. -/
theorem mem_span_yDegree_pow_iff {R : Type*} [Semiring R]
    (f : AddMonoidAlgebra R exponentMonoid) (k : ℕ) :
    f ∈ Ideal.span {(AddMonoidAlgebra.single yDegree (1 : R)) ^ k} ↔
      ∀ q ∈ f.coeff.support, k ≤ leftOrder q := by
  have hs : {(AddMonoidAlgebra.single yDegree (1 : R)) ^ k} =
      AddMonoidAlgebra.of' R exponentMonoid '' {k • yDegree} := by
    simp [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.of'_apply]
  rw [hs, AddMonoidAlgebra.mem_ideal_span_of'_image]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  simp_rw [add_comm _ (k • yDegree), ← le_leftOrder_iff]

/-- The quotient by `x^k` deletes exactly the monomials of right order at least `k`.
No domain or nontriviality assumption on the coefficient semiring is needed. -/
theorem mem_span_xDegree_pow_iff {R : Type*} [Semiring R]
    (f : AddMonoidAlgebra R exponentMonoid) (k : ℕ) :
    f ∈ Ideal.span {(AddMonoidAlgebra.single xDegree (1 : R)) ^ k} ↔
      ∀ q ∈ f.coeff.support, k ≤ rightOrder q := by
  have hs : {(AddMonoidAlgebra.single xDegree (1 : R)) ^ k} =
      AddMonoidAlgebra.of' R exponentMonoid '' {k • xDegree} := by
    simp [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.of'_apply]
  rw [hs, AddMonoidAlgebra.mem_ideal_span_of'_image]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  simp_rw [add_comm _ (k • xDegree), ← le_rightOrder_iff]

/-- The upper chart transition on exponents, `(a,b,h) ↦ (a,b-a,h)`. -/
def upperExponent : (ℤ × ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ × ℤ) :=
  (LinearEquiv.refl ℤ ℤ).skewProd (LinearEquiv.refl ℤ (ℤ × ℤ))
    ((-LinearMap.id).prod 0)

@[simp] theorem upperExponent_apply (q : ℤ × ℤ × ℤ) :
    upperExponent q = (q.1, q.2.1 - q.1, q.2.2) := by
  ext <;> simp [upperExponent, sub_eq_add_neg]

@[simp] theorem upperExponent_symm_apply (q : ℤ × ℤ × ℤ) :
    upperExponent.symm q = (q.1, q.2.1 + q.1, q.2.2) := by
  ext <;> simp [upperExponent]

/-- The chart change restricted to the coefficient exponent monoid. -/
def upperMonoid : exponentMonoid ≃+ exponentMonoid where
  toFun q := ⟨upperExponent q.val, by
    simpa only [upperExponent_apply, mem_exponentMonoid] using q.property⟩
  invFun q := ⟨upperExponent.symm q.val, by
    simpa only [mem_exponentMonoid, upperExponent_symm_apply] using q.property⟩
  left_inv q := Subtype.ext (upperExponent.symm_apply_apply q.val)
  right_inv q := Subtype.ext (upperExponent.apply_symm_apply q.val)
  map_add' q r := Subtype.ext (upperExponent.map_add q.val r.val)

@[simp] theorem coe_upperMonoid (q : exponentMonoid) :
    (upperMonoid q).val = upperExponent q.val := (rfl)

@[simp] theorem coe_upperMonoid_symm (q : exponentMonoid) :
    (upperMonoid.symm q).val = upperExponent.symm q.val := (rfl)

/-- In free monomial coordinates the upper shear changes only the Laurent exponent. -/
theorem exponentEquiv_upperMonoid (q : exponentMonoid) :
    exponentEquiv (upperMonoid q) =
      (q.val.2.1 + (rightOrder q : ℤ) - leftOrder q, leftOrder q, rightOrder q) := by
  have hl := natCast_leftOrder q
  have hr := natCast_rightOrder q
  ext <;> simp only [exponentEquiv_apply, coe_upperMonoid, upperExponent_apply,
    leftOrder_apply, rightOrder_apply]
  omega

/-- The upper chart sends `x` to `wx`. -/
@[simp] theorem upperMonoid_xDegree : upperMonoid xDegree = tangentDegree 1 + xDegree := by
  apply Subtype.ext
  simp

/-- The upper chart sends `y` to `w⁻¹y`. -/
@[simp] theorem upperMonoid_yDegree : upperMonoid yDegree = tangentDegree (-1) + yDegree := by
  apply Subtype.ext
  simp

@[simp] theorem upperMonoid_smoothingDegree : upperMonoid smoothingDegree = smoothingDegree := by
  apply Subtype.ext
  simp

@[simp] theorem upperMonoid_tangentDegree (b : ℤ) :
    upperMonoid (tangentDegree b) = tangentDegree b := by
  apply Subtype.ext
  simp

/-- Spatial direction forgets the smoothing exponent. -/
def exponentProjection : (ℤ × ℤ × ℤ) →ₗ[ℤ] ℤ × ℤ :=
  (LinearMap.fst ℤ ℤ (ℤ × ℤ)).prod
    ((LinearMap.fst ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ (ℤ × ℤ)))

/-- The upper transition on the tangent lattice, `(a,b) ↦ (a,b-a)`. -/
def upperTangent : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (LinearEquiv.refl ℤ ℤ).skewProd (LinearEquiv.refl ℤ ℤ) (-LinearMap.id)

@[simp] theorem exponentProjection_apply (q : ℤ × ℤ × ℤ) :
    exponentProjection q = (q.1, q.2.1) := (rfl)

@[simp] theorem upperTangent_apply (q : ℤ × ℤ) :
    upperTangent q = (q.1, q.2 - q.1) := by
  simp [upperTangent, sub_eq_add_neg]

@[simp] theorem upperTangent_symm_apply (q : ℤ × ℤ) :
    upperTangent.symm q = (q.1, q.2 + q.1) := by
  simp [upperTangent]

/-- Exponent transport and tangent transport give the same spatial direction. -/
theorem exponentProjection_upperExponent (q : ℤ × ℤ × ℤ) :
    exponentProjection (upperExponent q) = upperTangent (exponentProjection q) := by
  simp

end Mei.FocusFocus
