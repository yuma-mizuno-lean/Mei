/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Tangential
public import Mei.RingTheory.Node.Map

/-!
# Coefficient change for full-exponent slab correspondences

Changing the scalar coefficients of a slab preserves both normal and tangential
exponents, the two chamber maps, and the incoming lifts. The resulting morphism
of graded correspondences compares individual homogeneous transfers, including
coefficient quotients that kill the smoothing parameter or an incoming coefficient.

We use `TauCeti.NodeAlgebra.map`, `AddMonoidAlgebra.curryAlgEquiv_mapAlgHom`,
and `GradedCorrespondence.Hom`. The slab interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Definitions 3.1–3.3, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra
open scoped AlgebraMonoidAlgebra Mei.NodeAlgebra

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid M] (a : R[M])

local notation "a'" => algebraMap R[M] S[M] a
local notation "ψ" => AddMonoidAlgebra.mapAlgHom (ℤ × M) (Algebra.ofId R S)

-- Compose the existing scalar towers through the tangential coefficient algebra.
-- These local instances choose no new scalar action.
local instance : IsScalarTower R R[M] (NodeAlgebra S[M] a') :=
  IsScalarTower.to₁₂₄ R R[M] S[M] _

local instance : IsScalarTower R S (NodeAlgebra S[M] a') :=
  IsScalarTower.to₁₂₄ R S S[M] _

/-- Changing coefficients commutes with the left full-exponent chamber map. -/
theorem exponentLeftMap_map (x : NodeAlgebra R[M] a) :
    exponentLeftMap a' (TauCeti.NodeAlgebra.map (S := S[M]) a x) = ψ (exponentLeftMap a x) := by
  apply (curryAlgEquiv S).injective
  simp only [curry_exponentLeftMap, leftLaurentMap_map,
    curryAlgEquiv_mapAlgHom_ofId]

/-- Changing coefficients commutes with the right full-exponent chamber map. -/
theorem exponentRightMap_map (x : NodeAlgebra R[M] a) :
    exponentRightMap a' (TauCeti.NodeAlgebra.map (S := S[M]) a x) = ψ (exponentRightMap a x) := by
  apply (curryAlgEquiv S).injective
  simp only [curry_exponentRightMap, rightLaurentMap_map,
    curryAlgEquiv_mapAlgHom_ofId]

/-- Incoming lifts retain their normal and tangential exponents under coefficient change. -/
theorem map_exponentIncomingLift (i : Fin 2) (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) :
    TauCeti.NodeAlgebra.map (S := S[M]) a (exponentIncomingLift a i p u) =
      exponentIncomingLift a' i p
        ⟨ψ u, mapAlgHom_mem_gradeBy (Algebra.ofId R S) u.property⟩ := by
  simp only [exponentIncomingLift_apply, map_incomingLift,
    curryAlgEquiv_mapAlgHom_ofId]

/-- Scalar change is a morphism of slab correspondences retaining both exponent coordinates.
Its degree maps are identities, so transfers commute component by component. -/
def exponentCorrespondenceMap :
    GradedCorrespondence.Hom (exponentCorrespondence a)
      ((exponentCorrespondence a').restrictScalars R) id id where
  middle := ((Mei.NodeAlgebra.mapAlgHom (S := S[M]) a).restrictScalars R).toLinearMap
  left := (ψ).toLinearMap
  right := (ψ).toLinearMap
  left_comm := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, exponentCorrespondence_left,
      GradedCorrespondence.restrictScalars_left, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply,
      Mei.NodeAlgebra.mapAlgHom_apply] using (exponentLeftMap_map (S := S) a x).symm
  right_comm := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply, exponentCorrespondence_right,
      GradedCorrespondence.restrictScalars_right, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply,
      Mei.NodeAlgebra.mapAlgHom_apply] using (exponentRightMap_map (S := S) a x).symm
  left_mem _ _ hx := mapAlgHom_mem_gradeBy (Algebra.ofId R S) hx
  right_mem _ _ hx := mapAlgHom_mem_gradeBy (Algebra.ofId R S) hx
  admissible_left _ hx := hx
  admissible_right _ hx := hx
  middle_liftLeft p u := by
    simp only [exponentCorrespondence_liftLeft,
      GradedCorrespondence.restrictScalars_liftLeft_apply, AlgHom.toLinearMap_apply,
      AlgHom.restrictScalars_apply, Mei.NodeAlgebra.mapAlgHom_apply, id_eq]
    -- Identify the admissible subtype after applying the identity degree map.
    convert map_exponentIncomingLift (S := S) a 0 p u using 1
    congr 2
  middle_liftRight p u := by
    simp only [exponentCorrespondence_liftRight,
      GradedCorrespondence.restrictScalars_liftRight_apply, AlgHom.toLinearMap_apply,
      AlgHom.restrictScalars_apply, Mei.NodeAlgebra.mapAlgHom_apply, id_eq]
    convert map_exponentIncomingLift (S := S) a 1 p u using 1
    congr 2

@[simp]
theorem exponentCorrespondenceMap_middle :
    (exponentCorrespondenceMap (S := S) a).middle =
      ((Mei.NodeAlgebra.mapAlgHom (S := S[M]) a).restrictScalars R).toLinearMap := (rfl)

@[simp]
theorem exponentCorrespondenceMap_left :
    (exponentCorrespondenceMap (S := S) a).left = (ψ).toLinearMap := (rfl)

@[simp]
theorem exponentCorrespondenceMap_right :
    (exponentCorrespondenceMap (S := S) a).right = (ψ).toLinearMap := (rfl)

end Mei.NodeAlgebra
