/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.CoefficientDiagram

/-!
# Comparing the focus-focus coefficient diagrams

The inverse slab dictionary and the faithful chamber Laurent embeddings form a
natural transformation of algebra-valued incidence diagrams. Its three components
commute with changes of coefficients and cutoff reductions. Thus a matching
coefficient family in the nodal chambers gives a matching Laurent family using
the same maps that preserve homogeneous incoming lifts.

We assemble `chamberLaurentComparison` with Mathlib's `spanHomMk`, and reuse
`truncatedSlabMap_toSlabAlgebra` and the chamber Laurent realization squares.
The slab model follows Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Mei.NodeAlgebra

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open Mei.LaurentPolynomial

variable (K : Type*) [CommRing K]

local notation "S(" k ")" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ(" k ")" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)

-- Use the original K-action through the tangential Laurent coefficient ring.
local instance (k : ℕ) : IsScalarTower K (S(k)) (SlabNode (τ(k))) :=
  IsScalarTower.to₁₂₄ K (S(k)) (S(k))[ℤ] _

/-- The Laurent slab maps, with the coefficient ring and both exponent coordinates retained. -/
abbrev laurentSlabIncidence (k : ℕ) : WalkingSpan ⥤ AlgCat K :=
  span (AlgCat.ofHom ((exponentLeftMap (C (τ(k)) * (1 + T 1))).restrictScalars K))
    (AlgCat.ofHom ((exponentRightMap (C (τ(k)) * (1 + T 1))).restrictScalars K))

/-- The face object is the nodal slab with its original scalar action. -/
@[simp]
theorem laurentSlabIncidence_obj_zero (k : ℕ) :
    (laurentSlabIncidence K k).obj .zero = AlgCat.of K (SlabNode (τ(k))) := (rfl)

/-- The left chamber retains both Laurent exponents. -/
@[simp]
theorem laurentSlabIncidence_obj_left (k : ℕ) :
    (laurentSlabIncidence K k).obj .left = AlgCat.of K (S(k))[ℤ × ℤ] := (rfl)

/-- The right chamber uses the same Laurent coefficient algebra. -/
@[simp]
theorem laurentSlabIncidence_obj_right (k : ℕ) :
    (laurentSlabIncidence K k).obj .right = AlgCat.of K (S(k))[ℤ × ℤ] := (rfl)

/-- The left incidence is the left full-exponent slab map. -/
@[simp↓]
theorem laurentSlabIncidence_map_fst (k : ℕ) (z : SlabNode (τ(k))) :
    ((laurentSlabIncidence K k).map WalkingSpan.Hom.fst).hom z =
      exponentLeftMap (C (τ(k)) * (1 + T 1)) z := (rfl)

/-- The right incidence is the right full-exponent slab map. -/
@[simp↓]
theorem laurentSlabIncidence_map_snd (k : ℕ) (z : SlabNode (τ(k))) :
    ((laurentSlabIncidence K k).map WalkingSpan.Hom.snd).hom z =
      exponentRightMap (C (τ(k)) * (1 + T 1)) z := (rfl)

/-- The nodal coefficient diagram maps to the Laurent slab diagram by the inverse
slab dictionary and the two chamber embeddings. -/
def chamberLaurentIncidenceComparison (k : ℕ) :
    slabIncidence K k ⟶ laurentSlabIncidence K k :=
  spanHomMk
    (AlgCat.ofHom ((algebraEquiv (τ(k)) k
      (AdjoinRoot.root_X_pow_pow (k + 1))).symm.toAlgHom.restrictScalars K))
    (AlgCat.ofHom (leftChamberExponentMap K k))
    (AlgCat.ofHom (rightChamberExponentMap K k))
    (by
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro z
      simp only [AlgCat.hom_comp, AlgCat.hom_ofHom, AlgHom.comp_apply]
      rw [slabIncidence_map_fst]
      simpa only [LinearMap.comp_apply, chamberLaurentComparison_left,
        chamberLaurentComparison_middle, GradedCorrespondence.restrictScalars_left,
        exponentCorrespondence_left, AlgHom.toLinearMap_apply,
        LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.toAlgHom_apply,
        laurentSlabIncidence_map_fst, AlgHom.restrictScalars_apply] using
          LinearMap.congr_fun (chamberLaurentComparison K k).left_comm z)
    (by
      apply AlgCat.hom_ext
      apply AlgHom.ext
      intro z
      simp only [AlgCat.hom_comp, AlgCat.hom_ofHom, AlgHom.comp_apply]
      rw [slabIncidence_map_snd]
      simpa only [LinearMap.comp_apply, chamberLaurentComparison_right,
        chamberLaurentComparison_middle, GradedCorrespondence.restrictScalars_right,
        exponentCorrespondence_right, AlgHom.toLinearMap_apply,
        LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.toAlgHom_apply,
        laurentSlabIncidence_map_snd, AlgHom.restrictScalars_apply] using
          LinearMap.congr_fun (chamberLaurentComparison K k).right_comm z)

/-- The face comparison is exactly the inverse slab algebra dictionary. -/
@[simp↓]
theorem chamberLaurentIncidenceComparison_app_zero (k : ℕ)
    (z : slabAlgebra (C (τ(k))) (1 + T 1) k) :
    ((chamberLaurentIncidenceComparison K k).app .zero).hom z =
      (algebraEquiv (τ(k)) k (AdjoinRoot.root_X_pow_pow (k + 1))).symm z := (rfl)

/-- The left component is the faithful left Laurent realization. -/
@[simp↓]
theorem chamberLaurentIncidenceComparison_app_left (k : ℕ)
    (z : TruncatedExponentChamber K k 1) :
    ((chamberLaurentIncidenceComparison K k).app .left).hom z =
      leftChamberExponentMap K k z := (rfl)

/-- The right component is the faithful right Laurent realization. -/
@[simp↓]
theorem chamberLaurentIncidenceComparison_app_right (k : ℕ)
    (z : TruncatedExponentChamber K k 0) :
    ((chamberLaurentIncidenceComparison K k).app .right).hom z =
      rightChamberExponentMap K k z := (rfl)

variable {K} {K' : Type*} [CommRing K'] {k l : ℕ}
  (φ : K →+* K') (hl : l ≤ k)

local notation "S'" => AdjoinRoot (Polynomial.X ^ (l + 1) : Polynomial K')
local notation "τ'" => AdjoinRoot.root (Polynomial.X ^ (l + 1) : Polynomial K')

/-- The left comparison commutes with arbitrary coefficient maps and lower cutoffs,
including maps that kill homogeneous coefficients. -/
@[simp↓]
theorem leftChamberExponentMap_truncatedExponentChamberMap
    (z : TruncatedExponentChamber K k 1) :
    leftChamberExponentMap K' l (truncatedExponentChamberMap φ hl 1 z) =
      mapRingHom (ℤ × ℤ)
        (AdjoinRoot.map φ _ _ (by
          simpa using pow_dvd_pow (Polynomial.X : Polynomial K') (Nat.add_le_add_right hl 1)))
        (leftChamberExponentMap K k z) := by
  let ψ : S(k) →+* S' := AdjoinRoot.map φ _ _ (by
    simpa using pow_dvd_pow (Polynomial.X : Polynomial K') (Nat.add_le_add_right hl 1))
  let : Algebra (S(k)) S' := ψ.toAlgebra
  let : Algebra (S(k))[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  apply (curryAlgEquiv S').injective
  rw [leftChamberExponentMap_apply, AlgEquiv.apply_symm_apply]
  have hc := curryAlgEquiv_mapAlgHom_ofId (R := S(k)) (S := S')
    (leftChamberExponentMap K k z)
  rw [leftChamberExponentMap_apply, AlgEquiv.apply_symm_apply] at hc
  rw [truncatedExponentChamberMap_one]
  refine (leftChamberLaurentMap_leftChamberMap
    (truncatedScalarMap_C_root φ hl) hl (C_root_X_pow_pow K (k + 1))
    (C_root_X_pow_pow K' (l + 1)) z).trans ?_
  simpa only [← AlgHom.coe_toRingHom, _root_.AddMonoidAlgebra.toRingHom_mapAlgHom,
    Algebra.ofId,
    RingHom.algebraMap_toAlgebra, AddMonoidAlgebra.algebraMap_def, truncatedScalarMap_def, ψ,
    leftChamberExponentMap_apply] using hc.symm

/-- The right comparison obeys the same coefficient and cutoff square. -/
@[simp↓]
theorem rightChamberExponentMap_truncatedExponentChamberMap
    (z : TruncatedExponentChamber K k 0) :
    rightChamberExponentMap K' l (truncatedExponentChamberMap φ hl 0 z) =
      mapRingHom (ℤ × ℤ)
        (AdjoinRoot.map φ _ _ (by
          simpa using pow_dvd_pow (Polynomial.X : Polynomial K') (Nat.add_le_add_right hl 1)))
        (rightChamberExponentMap K k z) := by
  let ψ : S(k) →+* S' := AdjoinRoot.map φ _ _ (by
    simpa using pow_dvd_pow (Polynomial.X : Polynomial K') (Nat.add_le_add_right hl 1))
  let : Algebra (S(k)) S' := ψ.toAlgebra
  let : Algebra (S(k))[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  apply (curryAlgEquiv S').injective
  rw [rightChamberExponentMap_apply, AlgEquiv.apply_symm_apply]
  have hc := curryAlgEquiv_mapAlgHom_ofId (R := S(k)) (S := S')
    (rightChamberExponentMap K k z)
  rw [rightChamberExponentMap_apply, AlgEquiv.apply_symm_apply] at hc
  rw [truncatedExponentChamberMap_zero]
  refine (rightChamberLaurentMap_rightChamberMap
    (truncatedScalarMap_C_root φ hl) hl (C_root_X_pow_pow K (k + 1))
    (C_root_X_pow_pow K' (l + 1)) z).trans ?_
  simpa only [← AlgHom.coe_toRingHom, _root_.AddMonoidAlgebra.toRingHom_mapAlgHom,
    Algebra.ofId,
    RingHom.algebraMap_toAlgebra, AddMonoidAlgebra.algebraMap_def, truncatedScalarMap_def, ψ,
    rightChamberExponentMap_apply] using hc.symm

/-- The inverse slab dictionary commutes with coefficient changes and cutoff
reductions, on every matching pair. -/
@[simp↓]
theorem algebraEquiv_symm_truncatedSlabMap
    (z : slabAlgebra (C (τ(k))) (1 + T 1) k) :
    (algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))).symm
        (truncatedSlabMap φ hl z) =
      (letI : Algebra (S(k))[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
       mapOfEq (C (τ(k)) * (1 + T 1))
         (by simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
           truncatedScalarMap_C_root, truncatedScalarMap_T])
         ((algebraEquiv (τ(k)) k (AdjoinRoot.root_X_pow_pow (k + 1))).symm z)) := by
  apply (algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))).symm_apply_eq.mpr
  let e := algebraEquiv (τ(k)) k (AdjoinRoot.root_X_pow_pow (k + 1))
  let e' := algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))
  let : Algebra (S(k))[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  let htf : algebraMap (S(k))[ℤ] S'[ℤ] (C (τ(k)) * (1 + T 1)) =
      C τ' * (1 + T 1) := by
    simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
      truncatedScalarMap_C_root, truncatedScalarMap_T]
  have he : truncatedSlabMap φ hl (e (e.symm z)) =
      e' (mapOfEq (C (τ(k)) * (1 + T 1)) htf (e.symm z)) := by
    simpa only [e, e', algebraEquiv_apply] using
      truncatedSlabMap_toSlabAlgebra φ hl (e.symm z)
  simpa only [AlgEquiv.apply_symm_apply] using he

end Mei.FocusFocus
