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

end Mei.FocusFocus
