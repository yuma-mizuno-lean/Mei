/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.CoefficientDiagram
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Upper.Reduction

/-!
# Upper and lower focus-focus incidence towers

The upper slab and its chamber projections form an incidence diagram over the
original coefficient ring. The upper shear on the left chamber and the gluing
isomorphism on the slab identify this diagram with the lower incidence diagram.
Transporting cutoff reductions through this isomorphism gives the upper tower;
its components are the existing reductions on actual upper matching pairs and
chambers. The comparison is therefore natural at every cutoff, rather than only
an isomorphism of the individual slab algebras.

We use `upperSlabEquiv`, `upperChamberCorrespondence`, `slabIncidenceReduction`,
`truncatedUpperSlabMap` and Mathlib's `spanIsoMk` and `NatIso.ofComponents`.
The two crossing descriptions follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Mei.FocusFocus

open Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K]

local notation "τ(" k ")" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "R(" k ")" => AddMonoidAlgebra (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) ℤ
local notation "A(" k ")" => upperSlabAlgebra (τ(k)) k

/-- The upper crossing description as a span of algebras over the original
coefficient ring. Its two incidences are the upper slab's actual projections. -/
abbrev upperSlabIncidence (k : ℕ) : WalkingSpan ⥤ AlgCat K :=
  span
    (AlgCat.ofHom (((AlgHom.fst (R(k)) _ _).comp (A(k)).val).restrictScalars K))
    (AlgCat.ofHom (((AlgHom.snd (R(k)) _ _).comp (A(k)).val).restrictScalars K))

/-- The face object is the upper matching algebra. -/
@[simp]
theorem upperSlabIncidence_obj_zero (k : ℕ) :
    (upperSlabIncidence K k).obj .zero = AlgCat.of K A(k) := (rfl)

/-- The left chamber is expressed in its upper frame. -/
@[simp]
theorem upperSlabIncidence_obj_left (k : ℕ) :
    (upperSlabIncidence K k).obj .left = AlgCat.of K (TruncatedExponentChamber K k 1) := (rfl)

/-- The right chamber retains its original frame. -/
@[simp]
theorem upperSlabIncidence_obj_right (k : ℕ) :
    (upperSlabIncidence K k).obj .right = AlgCat.of K (TruncatedExponentChamber K k 0) := (rfl)

/-- The left incidence agrees with the homogeneous correspondence. -/
@[simp↓]
theorem upperSlabIncidence_map_fst (k : ℕ) (z : A(k)) :
    ((upperSlabIncidence K k).map WalkingSpan.Hom.fst).hom z =
      (upperChamberCorrespondence K k).left z := by
  rw [upperChamberCorrespondence_left_apply]
  rfl

/-- The right incidence agrees with the homogeneous correspondence. -/
@[simp↓]
theorem upperSlabIncidence_map_snd (k : ℕ) (z : A(k)) :
    ((upperSlabIncidence K k).map WalkingSpan.Hom.snd).hom z =
      (upperChamberCorrespondence K k).right z := by
  rw [upperChamberCorrespondence_right_apply]
  rfl

/-- The lower and upper incidence diagrams are isomorphic, shearing the left
chamber, applying the gluing comparison on the slab, and fixing the right chamber. -/
def slabIncidenceIso (k : ℕ) : slabIncidence K k ≅ upperSlabIncidence K k :=
  spanIsoMk
    ((upperSlabEquiv K k).restrictScalars K).toAlgebraIso
    (upperTruncatedExponentChamber K k 1).toAlgebraIso
    (Iso.refl _)
    (by ext z; simp)
    (by ext z; simp)

/-- The face comparison is the existing gluing isomorphism. -/
@[simp↓]
theorem slabIncidenceIso_hom_app_zero (k : ℕ)
    (z : slabAlgebra (C (τ(k))) (1 + T 1) k) :
    ((slabIncidenceIso K k).hom.app .zero).hom z = upperSlabEquiv K k z := (rfl)

/-- The left comparison is precisely the upper chamber shear. -/
@[simp↓]
theorem slabIncidenceIso_hom_app_left (k : ℕ)
    (z : TruncatedExponentChamber K k 1) :
    ((slabIncidenceIso K k).hom.app .left).hom z =
      upperTruncatedExponentChamber K k 1 z := (rfl)

/-- The right comparison fixes every coefficient. -/
@[simp↓]
theorem slabIncidenceIso_hom_app_right (k : ℕ)
    (z : TruncatedExponentChamber K k 0) :
    ((slabIncidenceIso K k).hom.app .right).hom z = z := (rfl)

/-- Returning from the upper face uses the inverse gluing comparison. -/
@[simp↓]
theorem slabIncidenceIso_inv_app_zero (k : ℕ) (z : A(k)) :
    ((slabIncidenceIso K k).inv.app .zero).hom z = (upperSlabEquiv K k).symm z := (rfl)

/-- Returning from the upper left chamber undoes its shear. -/
@[simp↓]
theorem slabIncidenceIso_inv_app_left (k : ℕ)
    (z : TruncatedExponentChamber K k 1) :
    ((slabIncidenceIso K k).inv.app .left).hom z =
      (upperTruncatedExponentChamber K k 1).symm z := (rfl)

/-- The inverse comparison also fixes the right chamber. -/
@[simp↓]
theorem slabIncidenceIso_inv_app_right (k : ℕ)
    (z : TruncatedExponentChamber K k 0) :
    ((slabIncidenceIso K k).inv.app .right).hom z = z := (rfl)

/-- Cutoff reduction of the upper span, transported from the lower span. -/
def upperSlabIncidenceReduction {k l : ℕ} (hl : l ≤ k) :
    upperSlabIncidence K k ⟶ upperSlabIncidence K l :=
  (slabIncidenceIso K k).inv ≫ slabIncidenceReduction K hl ≫ (slabIncidenceIso K l).hom

/-- The upper face transition is the reduction of actual upper matching pairs. -/
@[simp↓]
theorem upperSlabIncidenceReduction_app_zero {k l : ℕ} (hl : l ≤ k) (z : A(k)) :
    ((upperSlabIncidenceReduction K hl).app .zero).hom z =
      truncatedUpperSlabMap (RingHom.id K) hl z := by
  simp only [upperSlabIncidenceReduction, NatTrans.comp_app, AlgCat.hom_comp,
    AlgHom.comp_apply, slabIncidenceIso_hom_app_zero, slabIncidenceIso_inv_app_zero,
    slabIncidenceReduction_app_zero]
  exact (truncatedUpperSlabMap_upperSlabEquiv (RingHom.id K) hl
    ((upperSlabEquiv K k).symm z)).symm.trans (by simp)

/-- The left upper transition is the canonical chamber reduction; it commutes
with the change of frame, including elements killed by reduction. -/
@[simp↓]
theorem upperSlabIncidenceReduction_app_left {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 1) :
    ((upperSlabIncidenceReduction K hl).app .left).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 1 z := by
  simp only [upperSlabIncidenceReduction, NatTrans.comp_app, AlgCat.hom_comp,
    AlgHom.comp_apply, slabIncidenceIso_hom_app_left, slabIncidenceIso_inv_app_left,
    slabIncidenceReduction_app_left]
  exact (truncatedExponentChamberMap_upper K k 1 (RingHom.id K) hl
    ((upperTruncatedExponentChamber K k 1).symm z)).symm.trans (by simp)

/-- The right upper transition is the original right chamber reduction. -/
@[simp↓]
theorem upperSlabIncidenceReduction_app_right {k l : ℕ} (hl : l ≤ k)
    (z : TruncatedExponentChamber K k 0) :
    ((upperSlabIncidenceReduction K hl).app .right).hom z =
      truncatedExponentChamberMap (RingHom.id K) hl 0 z := by
  simp only [upperSlabIncidenceReduction, NatTrans.comp_app, AlgCat.hom_comp,
    AlgHom.comp_apply, slabIncidenceIso_hom_app_right, slabIncidenceIso_inv_app_right,
    slabIncidenceReduction_app_right]

/-- Reducing to the same cutoff fixes the entire upper incidence diagram. -/
@[simp]
theorem upperSlabIncidenceReduction_refl (k : ℕ) :
    upperSlabIncidenceReduction K (k := k) le_rfl = 𝟙 _ := by
  simp [upperSlabIncidenceReduction]

/-- Successive upper cutoff reductions compose. -/
theorem upperSlabIncidenceReduction_comp {k l m : ℕ} (hl : l ≤ k) (hm : m ≤ l) :
    upperSlabIncidenceReduction K hl ≫ upperSlabIncidenceReduction K hm =
      upperSlabIncidenceReduction K (hm.trans hl) := by
  simp only [upperSlabIncidenceReduction, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (slabIncidenceReduction K hl), slabIncidenceReduction_comp]

/-- The upper incidence diagrams form a tower over the original coefficient ring. -/
abbrev upperSlabIncidenceTower : ℕᵒᵖ ⥤ (WalkingSpan ⥤ AlgCat K) where
  obj k := upperSlabIncidence K k.unop
  map f := upperSlabIncidenceReduction K (leOfHom f.unop)
  map_id k := upperSlabIncidenceReduction_refl K k.unop
  map_comp f g :=
    (upperSlabIncidenceReduction_comp K (leOfHom f.unop) (leOfHom g.unop)).symm

/-- At each cutoff the upper tower is its explicit incidence span. -/
@[simp]
theorem upperSlabIncidenceTower_obj (k : ℕᵒᵖ) :
    (upperSlabIncidenceTower K).obj k = upperSlabIncidence K k.unop := (rfl)

/-- The arrows of the upper tower are the transported cutoff reductions. -/
@[simp]
theorem upperSlabIncidenceTower_map {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (upperSlabIncidenceTower K).map f =
      upperSlabIncidenceReduction K (leOfHom f.unop) := (rfl)

/-- Naturality of the whole incidence comparison under cutoff reduction. -/
@[reassoc (attr := simp)]
theorem slabIncidenceIso_hom_reduction {k l : ℕ} (hl : l ≤ k) :
    (slabIncidenceIso K k).hom ≫ upperSlabIncidenceReduction K hl =
      slabIncidenceReduction K hl ≫ (slabIncidenceIso K l).hom := by
  simp [upperSlabIncidenceReduction, ← Category.assoc]

/-- The two crossing descriptions give naturally isomorphic coefficient towers. -/
def slabIncidenceTowerIso : slabIncidenceTower K ≅ upperSlabIncidenceTower K :=
  NatIso.ofComponents (fun k => slabIncidenceIso K k.unop)
    (fun f => (slabIncidenceIso_hom_reduction K (leOfHom f.unop)).symm)

/-- Evaluation of the tower comparison is the explicit comparison of spans. -/
@[simp]
theorem slabIncidenceTowerIso_app (k : ℕᵒᵖ) :
    (slabIncidenceTowerIso K).app k = slabIncidenceIso K k.unop := (rfl)

end Mei.FocusFocus
