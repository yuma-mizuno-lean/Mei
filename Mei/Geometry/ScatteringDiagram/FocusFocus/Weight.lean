/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts
public import Mei.RingTheory.Node.Grading

/-!
# Horizontal weights and uniqueness of focus-focus lifts

The slab fiber product inherits the horizontal grading of
`S[w,w⁻¹][X,Y]/(XY-t(1+w))`, with `X` of weight `-1` and `Y` of weight `1`.
The left projection is injective on every nonpositive weight, and the right
projection on every nonnegative weight. Consequently the incoming lifts of
whole chamber exponent pieces are uniquely characterized by their source
projection and horizontal weight, including pieces killed by truncation.

We transport `NodeAlgebra.normalWeight` through `algebraEquiv` and use the
Laurent realization squares to detect equality. The coordinates and slab
interpretation follow Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable {S : Type*} [CommRing S] (t : S) (k : ℕ) (ht : t ^ (k + 1) = 0)

local notation "R" => S[T;T⁻¹]
local notation "A" => slabAlgebra (C t) (1 + T 1) k

/-- Horizontal weight on the actual slab fiber product; tangential coefficients
and the smoothing parameter have weight zero. -/
def horizontalWeight (n : ℤ) : Submodule R A :=
  (normalWeight (C t * (1 + T 1)) n).comap (algebraEquiv t k ht).symm.toLinearMap

/-- Horizontal homogeneity is detected by the nodal normal form. -/
theorem mem_horizontalWeight_iff (n : ℤ) (z : A) :
    z ∈ horizontalWeight t k ht n ↔
      (algebraEquiv t k ht).symm z ∈ normalWeight (C t * (1 + T 1)) n :=
  Submodule.mem_comap

/-- Every slab weight consists precisely of scalar multiples of its signed
nodal monomial, mapped into the fiber product. -/
@[simp]
theorem mem_horizontalWeight_iff_exists (n : ℤ) (z : A) :
    z ∈ horizontalWeight t k ht n ↔
      ∃ c : R, toSlabAlgebra (C t) (1 + T 1) k
        (c • signedMonomial (C t * (1 + T 1)) n) = z := by
  rw [mem_horizontalWeight_iff, mem_normalWeight_iff]
  apply exists_congr
  intro c
  rw [← algebraEquiv_apply t k ht]
  exact (algebraEquiv t k ht).eq_symm_apply

instance : SetLike.GradedMonoid (horizontalWeight t k ht) where
  one_mem := by
    rw [mem_horizontalWeight_iff, map_one]
    exact SetLike.GradedOne.one_mem
  mul_mem n m x y hx hy := by
    rw [mem_horizontalWeight_iff] at hx hy ⊢
    rw [map_mul]
    exact SetLike.mul_mem_graded hx hy

/-- The slab fiber product is the direct sum of its multiplicative horizontal weights. -/
instance : GradedAlgebra (horizontalWeight t k ht) :=
  DirectSum.IsInternal.gradedAlgebra <|
    TauCeti.DirectSum.isInternal_comap (normalWeight (C t * (1 + T 1)))
      (horizontalWeight t k ht) (algebraEquiv t k ht).symm.toLinearMap
      (algebraEquiv t k ht).symm.injective
      (fun _ _ => mem_horizontalWeight_iff t k ht _ _)
      (fun _ _ => (algebraEquiv t k ht).symm.surjective _)

/-- The left projection of the slab is injective on every incoming horizontal weight. -/
theorem fst_injOn_horizontalWeight (n : ℤ) (hn : n ≤ 0) :
    Set.InjOn (fun z : A => z.val.1) (horizontalWeight t k ht n) := by
  intro z hz w hw he
  obtain ⟨x, rfl⟩ := (algebraEquiv t k ht).surjective z
  obtain ⟨y, rfl⟩ := (algebraEquiv t k ht).surjective w
  have hx := (mem_horizontalWeight_iff t k ht n _).mp hz
  have hy := (mem_horizontalWeight_iff t k ht n _).mp hw
  rw [AlgEquiv.symm_apply_apply] at hx hy
  apply congrArg (algebraEquiv t k ht)
  apply leftLaurentMap_injOn_normalWeight _ n hn hx hy
  have h := congrArg (leftChamberLaurentMap (by rw [← map_pow, ht, map_zero])) he
  simpa only [algebraEquiv_apply, leftChamberLaurentMap_toSlabAlgebra] using h

/-- The right projection of the slab is injective on every incoming horizontal weight. -/
theorem snd_injOn_horizontalWeight (n : ℤ) (hn : 0 ≤ n) :
    Set.InjOn (fun z : A => z.val.2) (horizontalWeight t k ht n) := by
  intro z hz w hw he
  obtain ⟨x, rfl⟩ := (algebraEquiv t k ht).surjective z
  obtain ⟨y, rfl⟩ := (algebraEquiv t k ht).surjective w
  have hx := (mem_horizontalWeight_iff t k ht n _).mp hz
  have hy := (mem_horizontalWeight_iff t k ht n _).mp hw
  rw [AlgEquiv.symm_apply_apply] at hx hy
  apply congrArg (algebraEquiv t k ht)
  apply rightLaurentMap_injOn_normalWeight _ n hn hx hy
  have h := congrArg (rightChamberLaurentMap (by rw [← map_pow, ht, map_zero])) he
  simpa only [algebraEquiv_apply, rightChamberLaurentMap_toSlabAlgebra] using h

section Lifts

variable (K : Type*) [CommRing K]

local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)

/-- Every left incoming lift has the horizontal weight of its full exponent. -/
theorem leftChamberLift_mem_horizontalWeight (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    leftChamberLift K k q u ∈ horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1 := by
  rw [leftChamberLift_apply K k (C_root_X_pow_pow K (k + 1)),
    mem_horizontalWeight_iff_exists]
  refine ⟨(leftChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val).coeff (-q.val.1), ?_⟩
  have hq : q.val.1 = -((-q.val.1).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr q.property), neg_neg]
  have hm := congrArg (signedMonomial (C τ * (1 + T 1))) hq
  rw [signedMonomial_neg_natCast] at hm
  rw [hm]

/-- Every right incoming lift has the horizontal weight of its full exponent. -/
theorem rightChamberLift_mem_horizontalWeight (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    rightChamberLift K k q u ∈
      horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1 := by
  rw [rightChamberLift_apply K k (C_root_X_pow_pow K (k + 1)),
    mem_horizontalWeight_iff_exists]
  refine ⟨(rightChamberLaurentMap (C_root_X_pow_pow K (k + 1)) u.val).coeff q.val.1, ?_⟩
  have hq : q.val.1 = (q.val.1.toNat : ℤ) := (Int.toNat_of_nonneg q.property).symm
  have hm := congrArg (signedMonomial (C τ * (1 + T 1))) hq
  rw [signedMonomial_natCast] at hm
  rw [hm]

/-- A lift from the left is uniquely determined within its horizontal weight
by its entire source coefficient. -/
theorem eq_leftChamberLift_iff (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val)
    (z : slabAlgebra (C τ) (1 + T 1) k)
    (hz : z ∈ horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1) :
    z = leftChamberLift K k q u ↔ z.val.1 = u.val := by
  constructor
  · rintro rfl
    exact leftChamberLift_fst K k q u
  · intro he
    apply fst_injOn_horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1 q.property hz
      (leftChamberLift_mem_horizontalWeight k K q u)
    exact he.trans (leftChamberLift_fst K k q u).symm

/-- A lift from the right is uniquely determined within its horizontal weight
by its entire source coefficient. -/
theorem eq_rightChamberLift_iff (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val)
    (z : slabAlgebra (C τ) (1 + T 1) k)
    (hz : z ∈ horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1) :
    z = rightChamberLift K k q u ↔ z.val.2 = u.val := by
  constructor
  · rintro rfl
    exact rightChamberLift_snd K k q u
  · intro he
    apply snd_injOn_horizontalWeight τ k (AdjoinRoot.root_X_pow_pow (k + 1)) q.val.1 q.property hz
      (rightChamberLift_mem_horizontalWeight k K q u)
    exact he.trans (rightChamberLift_snd K k q u).symm

end Lifts

end Mei.FocusFocus
