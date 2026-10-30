/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Diagram
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Reduction
public import Mei.LinearAlgebra.GradedCorrespondence.Hom

/-!
# The focus-focus slab incidence tower

The slab and its two chamber projections form a diagram of algebras over the
original coefficient ring. Its cutoff transitions are the maps induced by the
gluing cospan, and preserve the full exponent gradings and chosen incoming lifts.
Thus homogeneous propagation and matching coefficients use the same reductions.

We assemble Mathlib's `spanHomMk` from the existing `slabConeIsLimit` and
`gluingCospanReduction`, and use `truncatedSlabMap_leftChamberLift` and its
right analogue to obtain morphisms of `chamberCorrespondence`. The geometric
model is Gross–Siebert, *An Invitation to Toric Degenerations*, §2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Mei.FocusFocus

open Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K]

local notation "τ(" k ")" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "A(" k ")" => slabAlgebra (C (τ(k))) (1 + T 1) k

/-- The coefficient face maps to its two adjacent chambers by the slab projections. -/
abbrev slabIncidence (k : ℕ) : WalkingSpan ⥤ AlgCat K :=
  span ((slabCone K k).π.app .left) ((slabCone K k).π.app .right)

/-- The middle object is the actual fiber-product slab. -/
@[simp]
theorem slabIncidence_obj_zero (k : ℕ) :
    (slabIncidence K k).obj .zero = AlgCat.of K A(k) := (rfl)

/-- The left object is the left chamber with its original scalar action. -/
@[simp]
theorem slabIncidence_obj_left (k : ℕ) :
    (slabIncidence K k).obj .left = AlgCat.of K (TruncatedExponentChamber K k 1) := (rfl)

/-- The right object is the right chamber with its original scalar action. -/
@[simp]
theorem slabIncidence_obj_right (k : ℕ) :
    (slabIncidence K k).obj .right = AlgCat.of K (TruncatedExponentChamber K k 0) := (rfl)

/-- The left incidence is the left leg of the homogeneous correspondence. -/
@[simp↓]
theorem slabIncidence_map_fst (k : ℕ) (z : A(k)) :
    ((slabIncidence K k).map WalkingSpan.Hom.fst).hom z =
      (chamberCorrespondence K k).left z := by
  rw [chamberCorrespondence_left_apply]
  exact Mei.NodeAlgebra.slabCone_π_left K _ _ k z

/-- The right incidence is the right leg of the homogeneous correspondence. -/
@[simp↓]
theorem slabIncidence_map_snd (k : ℕ) (z : A(k)) :
    ((slabIncidence K k).map WalkingSpan.Hom.snd).hom z =
      (chamberCorrespondence K k).right z := by
  rw [chamberCorrespondence_right_apply]
  exact Mei.NodeAlgebra.slabCone_π_right K _ _ k z

/-- Cutoff reduction on the slab and both chambers, commuting with incidences. -/
def slabIncidenceReduction {k l : ℕ} (hl : l ≤ k) :
    slabIncidence K k ⟶ slabIncidence K l :=
  spanHomMk ((slabConeIsLimit K l).map (slabCone K k) (gluingCospanReduction K hl))
    ((gluingCospanReduction K hl).app .left) ((gluingCospanReduction K hl).app .right)
    (IsLimit.map_π (slabCone K k) (slabConeIsLimit K l)
      (gluingCospanReduction K hl) .left).symm
    (IsLimit.map_π (slabCone K k) (slabConeIsLimit K l)
      (gluingCospanReduction K hl) .right).symm

/-- The face transition is the existing reduction of matching pairs. -/
@[simp↓]
theorem slabIncidenceReduction_app_zero {k l : ℕ} (hl : l ≤ k) (z : A(k)) :
    ((slabIncidenceReduction K hl).app .zero).hom z =
      truncatedSlabMap (RingHom.id K) hl z :=
  slabConeIsLimit_map_apply K hl z

/-- The left chamber transition is the existing graded quotient reduction. -/
@[simp↓]
theorem slabIncidenceReduction_app_left {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 1) :
    ((slabIncidenceReduction K hl).app .left).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 1 z :=
  gluingCospanReduction_app_left K hl z

/-- The right chamber transition is the existing graded quotient reduction. -/
@[simp↓]
theorem slabIncidenceReduction_app_right {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    ((slabIncidenceReduction K hl).app .right).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 0 z :=
  gluingCospanReduction_app_right K hl z

/-- Reduction at the same cutoff is the identity on the entire incidence diagram. -/
@[simp]
theorem slabIncidenceReduction_refl (k : ℕ) :
    slabIncidenceReduction K (k := k) le_rfl = 𝟙 _ := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _) <;> apply AlgCat.hom_ext <;> ext z <;> simp

/-- Successive cutoff reductions compose on all coefficient objects. -/
theorem slabIncidenceReduction_comp {k l m : ℕ} (hl : l ≤ k) (hm : m ≤ l) :
    slabIncidenceReduction K hl ≫ slabIncidenceReduction K hm =
      slabIncidenceReduction K (hm.trans hl) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _) <;> apply AlgCat.hom_ext <;> apply AlgHom.ext <;> intro z
  · simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      slabIncidenceReduction_app_zero]
    simpa using RingHom.congr_fun
      (truncatedSlabMap_comp (RingHom.id K) hl (RingHom.id K) hm) z
  · simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      slabIncidenceReduction_app_left]
    simpa using RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 1 (RingHom.id K) hm) z
  · simp only [NatTrans.comp_app, AlgCat.hom_comp, AlgHom.comp_apply,
      slabIncidenceReduction_app_right]
    simpa using RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 0 (RingHom.id K) hm) z

/-- The slab incidence diagrams form a tower over the original coefficient ring. -/
abbrev slabIncidenceTower : ℕᵒᵖ ⥤ (WalkingSpan ⥤ AlgCat K) where
  obj k := slabIncidence K k.unop
  map f := slabIncidenceReduction K (leOfHom f.unop)
  map_id k := slabIncidenceReduction_refl K k.unop
  map_comp f g := (slabIncidenceReduction_comp K (leOfHom f.unop) (leOfHom g.unop)).symm

/-- Evaluation at a cutoff gives its slab incidence diagram. -/
@[simp]
theorem slabIncidenceTower_obj (k : ℕᵒᵖ) :
    (slabIncidenceTower K).obj k = slabIncidence K k.unop := (rfl)

/-- Tower arrows are exactly the prescribed reductions of all three objects. -/
@[simp]
theorem slabIncidenceTower_map {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (slabIncidenceTower K).map f = slabIncidenceReduction K (leOfHom f.unop) := (rfl)

/-- The incidence transition preserves both homogeneous gradings and incoming lifts. -/
def chamberCorrespondenceReduction {k l : ℕ} (hl : l ≤ k) :
    GradedCorrespondence.Hom (chamberCorrespondence K k) (chamberCorrespondence K l)
      _root_.id _root_.id where
  middle := ((slabIncidenceReduction K hl).app .zero).hom.toLinearMap
  left := ((slabIncidenceReduction K hl).app .left).hom.toLinearMap
  right := ((slabIncidenceReduction K hl).app .right).hom.toLinearMap
  left_comm := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      chamberCorrespondence_left_apply]
    rw [slabIncidenceReduction_app_left K hl z.val.1,
      slabIncidenceReduction_app_zero K hl z, truncatedSlabMap_fst]
  right_comm := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      chamberCorrespondence_right_apply]
    rw [slabIncidenceReduction_app_right K hl z.val.2,
      slabIncidenceReduction_app_zero K hl z, truncatedSlabMap_snd]
  left_mem q z hz := by
    simp only [AlgHom.toLinearMap_apply, id_eq]
    rw [slabIncidenceReduction_app_left K hl z]
    simpa only [← GradedRingHom.coe_toRingHom,
      truncatedExponentChamberGradedMap_toRingHom] using
      (truncatedExponentChamberGradedMap (RingHom.id K) hl 1).map_mem hz
  right_mem q z hz := by
    simp only [AlgHom.toLinearMap_apply, id_eq]
    rw [slabIncidenceReduction_app_right K hl z]
    simpa only [← GradedRingHom.coe_toRingHom,
      truncatedExponentChamberGradedMap_toRingHom] using
      (truncatedExponentChamberGradedMap (RingHom.id K) hl 0).map_mem hz
  admissible_left _ h := h
  admissible_right _ h := h
  middle_liftLeft q a := by
    simp only [AlgHom.toLinearMap_apply, chamberCorrespondence_liftLeft]
    refine (slabIncidenceReduction_app_zero K hl _).trans
      ((truncatedSlabMap_leftChamberLift (RingHom.id K) hl q a).trans ?_)
    apply congrArg (leftChamberLift K l q)
    apply Subtype.ext
    simp only [GradedRingHom.gradedAddHom_apply_coe, ← GradedRingHom.coe_toRingHom,
      truncatedExponentChamberGradedMap_toRingHom]
    exact (slabIncidenceReduction_app_left K hl a.val).symm
  middle_liftRight q a := by
    simp only [AlgHom.toLinearMap_apply, chamberCorrespondence_liftRight]
    refine (slabIncidenceReduction_app_zero K hl _).trans
      ((truncatedSlabMap_rightChamberLift (RingHom.id K) hl q a).trans ?_)
    apply congrArg (rightChamberLift K l q)
    apply Subtype.ext
    simp only [GradedRingHom.gradedAddHom_apply_coe, ← GradedRingHom.coe_toRingHom,
      truncatedExponentChamberGradedMap_toRingHom]
    exact (slabIncidenceReduction_app_right K hl a.val).symm

/-- The morphism of homogeneous correspondences uses the actual slab reduction. -/
@[simp]
theorem chamberCorrespondenceReduction_middle {k l : ℕ} (hl : l ≤ k) (z : A(k)) :
    (chamberCorrespondenceReduction K hl).middle z =
      truncatedSlabMap (RingHom.id K) hl z :=
  slabIncidenceReduction_app_zero K hl z

/-- Its left map is the same map as the left incidence transition. -/
@[simp]
theorem chamberCorrespondenceReduction_left {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 1) :
    (chamberCorrespondenceReduction K hl).left z =
      truncatedExponentChamberMap (RingHom.id K) hl 1 z :=
  slabIncidenceReduction_app_left K hl z

/-- Its right map is the same map as the right incidence transition. -/
@[simp]
theorem chamberCorrespondenceReduction_right {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    (chamberCorrespondenceReduction K hl).right z =
      truncatedExponentChamberMap (RingHom.id K) hl 0 z :=
  slabIncidenceReduction_app_right K hl z

/-- At a fixed cutoff all correspondence data, including lifts, are unchanged. -/
@[simp]
theorem chamberCorrespondenceReduction_refl (k : ℕ) :
    chamberCorrespondenceReduction K (k := k) le_rfl =
      GradedCorrespondence.Hom.id (chamberCorrespondence K k) := by
  apply GradedCorrespondence.Hom.ext <;> apply LinearMap.ext <;> intro z <;> simp

/-- Homogeneous correspondence transitions obey the same tower composition law. -/
theorem chamberCorrespondenceReduction_comp {k l m : ℕ} (hl : l ≤ k) (hm : m ≤ l) :
    (chamberCorrespondenceReduction K hm).comp (chamberCorrespondenceReduction K hl) =
      chamberCorrespondenceReduction K (hm.trans hl) := by
  apply GradedCorrespondence.Hom.ext <;> apply LinearMap.ext <;> intro z
  · simp only [GradedCorrespondence.Hom.comp_middle, LinearMap.comp_apply,
      chamberCorrespondenceReduction_middle]
    exact RingHom.congr_fun
      (truncatedSlabMap_comp (RingHom.id K) hl (RingHom.id K) hm) z
  · simp only [GradedCorrespondence.Hom.comp_left, LinearMap.comp_apply,
      chamberCorrespondenceReduction_left]
    exact RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 1 (RingHom.id K) hm) z
  · simp only [GradedCorrespondence.Hom.comp_right, LinearMap.comp_apply,
      chamberCorrespondenceReduction_right]
    exact RingHom.congr_fun
      (truncatedExponentChamberMap_comp (RingHom.id K) hl 0 (RingHom.id K) hm) z

end Mei.FocusFocus
