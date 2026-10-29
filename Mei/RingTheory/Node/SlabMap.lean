/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.RingTheory.Node.Gluing
public import Mei.RingTheory.Node.Map
public import Mei.RingTheory.Node.ScalarTower

/-!
# Coefficient change and truncation of slab algebras

Let `R'` be an `R`-algebra, and let `t, f : R` map to `t', f' : R'`. For `k' ≤ k`, the
coefficient map `R[x,y]/(xy-t) → R'[x,y]/(xy-t')` descends to the truncated chambers, the
overlap and the localized overlap of `Mei.NodeAlgebra.slabAlgebra`, from order `k` over `R` to
order `k'` over `R'`. These maps commute with both gluing maps, so they induce a map of slab
algebras `slabAlgebra t f k → slabAlgebra t' f' k'`. It is compatible with the comparison map
from the nodal algebra `R[X,Y]/(XY - tf)`, and hence with `Mei.NodeAlgebra.slabEquiv`.

A change of coefficients `K → K'` and the truncation `K[t]/(t^(k+2)) → K[t]/(t^(k+1))` are both
instances, so the comparison isomorphisms of the truncated slabs commute with both operations.
For the focus-focus slab of Gross–Siebert, *An invitation to toric degenerations*, §2.3,
arXiv:0808.2749v2, see `Mei.FocusFocus.slabAlgebraMap_algebraEquiv`.

## Main definitions

* `Mei.NodeAlgebra.mapOfEq`: the coefficient map `R[x,y]/(xy-a) → R'[x,y]/(xy-a')` when `a`
  maps to `a'`.
* `Mei.NodeAlgebra.slabAlgebraMap`: the induced map of slab algebras.

## Main results

* `Mei.NodeAlgebra.slabAlgebraMap_toSlabAlgebra` and `Mei.NodeAlgebra.slabAlgebraMap_slabEquiv`:
  the slab comparison commutes with coefficient change and truncation.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra
open scoped Mei.NodeAlgebra

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']

section MapOfEq

variable (a : R) {a' : R'} (h : algebraMap R R' a = a')

/-- The coefficient map `R[x,y]/(xy-a) → R'[x,y]/(xy-a')`, `x ↦ x`, `y ↦ y`, when `a` maps
to `a'`. -/
def mapOfEq : NodeAlgebra R a →ₐ[R] NodeAlgebra R' a' :=
  lift a (coord a' 0) (coord a' 1) (by
    rw [coord_zero_mul_coord_one, IsScalarTower.algebraMap_apply R R', h])

/-- `mapOfEq` fixes both coordinates. -/
@[simp]
theorem mapOfEq_coord (i : Fin 2) : mapOfEq a h (coord a i) = coord a' i := by
  fin_cases i <;> simp [mapOfEq]

/-- For `a' = algebraMap R R' a`, `mapOfEq` is the coefficient map `TauCeti.NodeAlgebra.map`. -/
theorem mapOfEq_rfl : mapOfEq a (rfl : algebraMap R R' a = _) = mapAlgHom a := by
  ext <;> simp

end MapOfEq

variable (t f : R) {t' f' : R'} (ht : algebraMap R R' t = t') (hf : algebraMap R R' f = f')
  {k k' : ℕ} (hk : k' ≤ k)

include hk in
/-- The image of `z^(k+1)` lies in `(z^(k'+1))` for a coordinate `z`, when `k' ≤ k`. -/
private theorem mapOfEq_coord_pow_mem (i : Fin 2) :
    mapOfEq t ht (coord t i ^ (k + 1)) ∈ Ideal.span {coord t' i ^ (k' + 1)} := by
  rw [map_pow, mapOfEq_coord, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ (by omega)

include hk in
private theorem span_coord_pow_le (i : Fin 2) :
    Ideal.span {coord t i ^ (k + 1)} ≤
      (Ideal.span {coord t' i ^ (k' + 1)}).comap (mapOfEq t ht) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact mapOfEq_coord_pow_mem t ht hk i

include hk in
private theorem span_pair_le :
    Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} ≤
      (Ideal.span {coord t' 0 ^ (k' + 1), coord t' 1 ^ (k' + 1)}).comap (mapOfEq t ht) := by
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, Ideal.mem_comap]
  · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      (mapOfEq_coord_pow_mem t ht hk 0)
  · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
      (mapOfEq_coord_pow_mem t ht hk 1)

/-- Coefficient change and truncation of the left chamber, from
`R[x,y]/(xy-t, y^(k+1))` to `R'[x,y]/(xy-t', y^(k'+1))`. -/
def leftChamberMap : LeftChamber t k →ₐ[R] LeftChamber t' k' :=
  Ideal.quotientMapₐ _ (mapOfEq t ht) (span_coord_pow_le t ht hk 1)

/-- Coefficient change and truncation of the right chamber, from
`R[x,y]/(xy-t, x^(k+1))` to `R'[x,y]/(xy-t', x^(k'+1))`. -/
def rightChamberMap : RightChamber t k →ₐ[R] RightChamber t' k' :=
  Ideal.quotientMapₐ _ (mapOfEq t ht) (span_coord_pow_le t ht hk 0)

/-- Coefficient change and truncation of the overlap, from
`R[x,y]/(xy-t, x^(k+1), y^(k+1))` to `R'[x,y]/(xy-t', x^(k'+1), y^(k'+1))`. -/
def overlapMap : Overlap t k →ₐ[R] Overlap t' k' :=
  Ideal.quotientMapₐ _ (mapOfEq t ht) (span_pair_le t ht hk)

@[simp]
theorem leftChamberMap_mk (z : NodeAlgebra R t) :
    leftChamberMap t ht hk (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (mapOfEq t ht z) := (rfl)

@[simp]
theorem rightChamberMap_mk (z : NodeAlgebra R t) :
    rightChamberMap t ht hk (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (mapOfEq t ht z) := (rfl)

@[simp]
theorem overlapMap_mk (z : NodeAlgebra R t) :
    overlapMap t ht hk (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (mapOfEq t ht z) := (rfl)

private theorem overlapMap_algebraMap (r : R) :
    overlapMap t ht hk (algebraMap R (Overlap t k) r) =
      algebraMap R' (Overlap t' k') (algebraMap R R' r) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R']

include hf in
private theorem powers_le_comap_overlapMap :
    Submonoid.powers (algebraMap R (Overlap t k) f) ≤
      (Submonoid.powers (algebraMap R' (Overlap t' k') f')).comap (overlapMap t ht hk) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow, overlapMap_algebraMap, hf]⟩

/-- Coefficient change and truncation of the overlap with `f` inverted. -/
def localizedOverlapMap : LocalizedOverlap t f k →ₐ[R] LocalizedOverlap t' f' k' where
  __ := IsLocalization.map (LocalizedOverlap t' f' k') (overlapMap t ht hk).toRingHom
    (powers_le_comap_overlapMap t f ht hf hk)
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (Overlap t k) (LocalizedOverlap t f k) r,
      IsScalarTower.algebraMap_apply R (Overlap t' k') (LocalizedOverlap t' f' k') r,
      ← AlgHom.commutes (overlapMap t ht hk)]
    exact IsLocalization.map_eq _ _

/-- The localized overlap map extends the overlap map. -/
@[simp]
theorem localizedOverlapMap_algebraMap (z : Overlap t k) :
    localizedOverlapMap t f ht hf hk (algebraMap _ _ z) =
      algebraMap _ (LocalizedOverlap t' f' k') (overlapMap t ht hk z) :=
  IsLocalization.map_eq (S := LocalizedOverlap t f k) (powers_le_comap_overlapMap t f ht hf hk) z

/-- The localized overlap map sends `f⁻¹` to `f'⁻¹`. -/
@[simp]
theorem localizedOverlapMap_invSelf :
    localizedOverlapMap t f ht hf hk (IsLocalization.Away.invSelf (algebraMap R (Overlap t k) f)) =
      IsLocalization.Away.invSelf (algebraMap R' (Overlap t' k') f') := by
  have h₁ := congrArg (localizedOverlapMap t f ht hf hk)
    (IsLocalization.Away.mul_invSelf (S := LocalizedOverlap t f k) (algebraMap R (Overlap t k) f))
  rw [map_mul, map_one, localizedOverlapMap_algebraMap, overlapMap_algebraMap, hf] at h₁
  have h₂ := IsLocalization.Away.mul_invSelf (S := LocalizedOverlap t' f' k')
    (algebraMap R' (Overlap t' k') f')
  linear_combination IsLocalization.Away.invSelf (algebraMap R' (Overlap t' k') f') * h₁ -
    localizedOverlapMap t f ht hf hk
      (IsLocalization.Away.invSelf (algebraMap R (Overlap t k) f)) * h₂

/-- Coefficient change and truncation commute with the left gluing map. -/
theorem localizedOverlapMap_leftGluing (z : LeftChamber t k) :
    localizedOverlapMap t f ht hf hk (leftGluing t f k z) =
      leftGluing t' f' k' (leftChamberMap t ht hk z) := by
  have h : (localizedOverlapMap t f ht hf hk).comp (leftGluing t f k) =
      ((leftGluing t' f' k').restrictScalars R).comp (leftChamberMap t ht hk) := by
    apply Ideal.Quotient.algHom_ext
    ext
    · simp [IsScalarTower.algebraMap_apply R R' (LocalizedOverlap t' f' k'), hf]
    · simp
  exact AlgHom.congr_fun h z

/-- Coefficient change and truncation commute with the right gluing map. -/
theorem localizedOverlapMap_rightGluing (z : RightChamber t k) :
    localizedOverlapMap t f ht hf hk (rightGluing t f k z) =
      rightGluing t' f' k' (rightChamberMap t ht hk z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp

/-- Coefficient change and truncation of slab algebras, from `slabAlgebra t f k` over `R` to
`slabAlgebra t' f' k'` over `R'`, acting by `leftChamberMap` and `rightChamberMap`. -/
def slabAlgebraMap : slabAlgebra t f k →ₐ[R] slabAlgebra t' f' k' :=
  AlgHom.codRestrict (((leftChamberMap t ht hk).prodMap (rightChamberMap t ht hk)).comp
    (slabAlgebra t f k).val) ((slabAlgebra t' f' k').restrictScalars R) fun p => by
      rw [Subalgebra.mem_restrictScalars, mem_slabAlgebra_iff]
      exact (localizedOverlapMap_leftGluing t f ht hf hk _).symm.trans
        ((congrArg _ ((mem_slabAlgebra_iff t f k).mp p.2)).trans
          (localizedOverlapMap_rightGluing t f ht hf hk _))

/-- The slab algebra map acts by the two chamber maps. -/
@[simp]
theorem coe_slabAlgebraMap (p : slabAlgebra t f k) :
    (slabAlgebraMap t f ht hf hk p : LeftChamber t' k' × RightChamber t' k') =
      (leftChamberMap t ht hk (p : LeftChamber t k × RightChamber t k).1,
        rightChamberMap t ht hk (p : LeftChamber t k × RightChamber t k).2) := (rfl)

/-- **Coefficient change and truncation of the slab comparison.** The comparison maps from the
nodal algebras `R[X,Y]/(XY - tf)` and `R'[X,Y]/(XY - t'f')` intertwine the coefficient map
with `slabAlgebraMap`. -/
theorem slabAlgebraMap_toSlabAlgebra (z : NodeAlgebra R (t * f)) :
    slabAlgebraMap t f ht hf hk (toSlabAlgebra t f k z) =
      toSlabAlgebra t' f' k' (mapOfEq (t * f) (by rw [map_mul, ht, hf]) z) := by
  have h : (slabAlgebraMap t f ht hf hk).comp (toSlabAlgebra t f k) =
      ((toSlabAlgebra t' f' k').restrictScalars R).comp
        (mapOfEq (t * f) (by rw [map_mul, ht, hf])) := by
    ext <;> simp [IsScalarTower.algebraMap_apply R R' (LeftChamber t' k'),
      IsScalarTower.algebraMap_apply R R' (RightChamber t' k'), hf]
  exact AlgHom.congr_fun h z

/-- `slabEquiv` commutes with coefficient change and truncation. -/
theorem slabAlgebraMap_slabEquiv (ht₀ : t ^ (k + 1) = 0)
    (hf₀ : ∀ (j : ℕ) (c : R), t ^ j ∣ f * c → t ^ j ∣ c) (ht₀' : t' ^ (k' + 1) = 0)
    (hf₀' : ∀ (j : ℕ) (c : R'), t' ^ j ∣ f' * c → t' ^ j ∣ c) (z : NodeAlgebra R (t * f)) :
    slabAlgebraMap t f ht hf hk (slabEquiv f ht₀ hf₀ z) =
      slabEquiv f' ht₀' hf₀' (mapOfEq (t * f) (by rw [map_mul, ht, hf]) z) := by
  rw [slabEquiv_apply, slabEquiv_apply, slabAlgebraMap_toSlabAlgebra]

end Mei.NodeAlgebra
