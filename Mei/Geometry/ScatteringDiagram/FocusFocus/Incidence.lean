/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Upper.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Overlap
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Lifts

/-!
# Upper gluing of the focus-focus chambers

The upper shear of a chamber descends to the upper change on its doubly
truncated overlap. Consequently the lower left incidence equals the upper
wall incidence after shearing the left chamber. The right chamber stays in
its original frame. These equations identify the fiber products defined by
the two crossing descriptions, including their actual chamber projections.
The upper slab carries admissible lifts of entire exponent pieces, and the
gluing comparison preserves lifts and homogeneous transfers, shearing the
left degree and retaining the right degree.

The construction uses `upperTruncatedExponentChamber`, `upperOverlap`,
`lowerWallMap_eq_upperWallMap_comp_upperOverlap`, `leftChamberLift`,
`rightChamberLift` and `GradedCorrespondence.Hom.transfer_map_of_injective`,
with Mathlib's equalizer subalgebras and `AlgEquiv.subalgebraMap`.
The coordinate and gluing conventions follow Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

section UpperPresentation

variable {S : Type*} [CommRing S] (t : S) (k : ℕ)

local notation "R" => S[T;T⁻¹]
local notation "D" => LocalizedOverlap (C t) (1 + T 1) k

/-- The left chamber incidence in the upper frame, with wall function `1+w⁻¹`
and values in the common localization at `1+w`. -/
def upperLeftGluing : LeftChamber (C t) k →ₐ[R] D :=
  (upperWallMap t k).comp (leftToOverlap (C t) k)

/-- The upper incidence on a chamber representative is the upper wall map. -/
@[simp]
theorem upperLeftGluing_mk (z : NodeAlgebra R (C t)) :
    upperLeftGluing t k (Ideal.Quotient.mk _ z) =
      upperWallMap t k (Ideal.Quotient.mk _ z) := by
  simp only [upperLeftGluing, AlgHom.comp_apply, leftToOverlap_mk]

/-- The slab coefficient algebra in the upper left frame and the unchanged
right frame, glued in the common localized overlap. -/
def upperSlabAlgebra : Subalgebra R (LeftChamber (C t) k × RightChamber (C t) k) :=
  AlgHom.equalizer ((upperLeftGluing t k).comp (AlgHom.fst R _ _))
    ((rightGluing (C t) (1 + T 1) k).comp (AlgHom.snd R _ _))

/-- Upper slab coefficients are exactly pairs with equal upper incidence images. -/
@[simp]
theorem mem_upperSlabAlgebra_iff (z : LeftChamber (C t) k × RightChamber (C t) k) :
    z ∈ upperSlabAlgebra t k ↔
      upperLeftGluing t k z.1 = rightGluing (C t) (1 + T 1) k z.2 := (Iff.rfl)

end UpperPresentation

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "R" => S[T;T⁻¹]

/-- The left chamber shear commutes with the actual quotient to the overlap. -/
@[simp]
theorem leftToOverlap_upper (x : TruncatedExponentChamber K k 1) :
    leftToOverlap (C τ) k (upperTruncatedExponentChamber K k 1 x) =
      upperOverlap τ k (leftToOverlap (C τ) k x) := by
  have he : (leftToOverlap (C τ) k).comp (upperTruncatedExponentChamberₐ K k 1).toAlgHom =
      (upperOverlap τ k).toAlgHom.comp (leftToOverlap (C τ) k) := by
    apply Ideal.Quotient.algHom_ext
    ext <;> simp
  simpa using AlgHom.congr_fun he x

/-- The right chamber shear also commutes with its quotient to the overlap.
This is the overlap square for a change of the right frame. -/
@[simp]
theorem rightToOverlap_upper (x : TruncatedExponentChamber K k 0) :
    rightToOverlap (C τ) k (upperTruncatedExponentChamber K k 0 x) =
      upperOverlap τ k (rightToOverlap (C τ) k x) := by
  have he : (rightToOverlap (C τ) k).comp (upperTruncatedExponentChamberₐ K k 0).toAlgHom =
      (upperOverlap τ k).toAlgHom.comp (rightToOverlap (C τ) k) := by
    apply Ideal.Quotient.algHom_ext
    ext <;> simp
  simpa using AlgHom.congr_fun he x

/-- The upper crossing after the left chamber shear equals the lower incidence
on every chamber element, including classes killed by the overlap quotient. -/
@[simp]
theorem upperLeftGluing_upper (x : TruncatedExponentChamber K k 1) :
    upperLeftGluing τ k (upperTruncatedExponentChamber K k 1 x) =
      leftGluing (C τ) (1 + T 1) k x := by
  calc
    _ = upperWallMap τ k (upperOverlap τ k (leftToOverlap (C τ) k x)) := by
      simp only [upperLeftGluing, AlgHom.comp_apply, leftToOverlap_upper]
    _ = lowerWallMap τ k (leftToOverlap (C τ) k x) :=
      (AlgHom.congr_fun (lowerWallMap_eq_upperWallMap_comp_upperOverlap τ k) _).symm
    _ = _ := AlgHom.congr_fun (lowerWallMap_comp_leftToOverlap τ k) x

/-- The lower and upper slab presentations are isomorphic by the upper shear
on the left chamber and the identity on the right. The equivalence fixes the
entire Laurent coefficient algebra over the truncated smoothing ring. -/
def upperSlabEquiv :
    slabAlgebra (C τ) (1 + T 1) k ≃ₐ[R] upperSlabAlgebra τ k := by
  let f := AlgEquiv.prodCongr (upperTruncatedExponentChamberₐ K k 1) (AlgEquiv.refl :
    TruncatedExponentChamber K k 0 ≃ₐ[R] TruncatedExponentChamber K k 0)
  have hcomap : slabAlgebra (C τ) (1 + T 1) k =
      (upperSlabAlgebra τ k).comap f.toAlgHom := by
    ext z
    simp [f]
  have hmap : (slabAlgebra (C τ) (1 + T 1) k).map f.toAlgHom =
      upperSlabAlgebra τ k := by
    rw [hcomap]
    exact Subalgebra.map_comap_eq_self_of_surjective f.surjective _
  exact (f.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ hmap)

/-- The upper gluing comparison shears precisely the left entry. -/
@[simp]
theorem coe_upperSlabEquiv (z : slabAlgebra (C τ) (1 + T 1) k) :
    (upperSlabEquiv K k z).val =
      (upperTruncatedExponentChamber K k 1 z.val.1, z.val.2) := by
  simp [upperSlabEquiv, Prod.map]

/-- Returning to the lower presentation applies the inverse shear on the left. -/
@[simp]
theorem coe_upperSlabEquiv_symm (z : upperSlabAlgebra τ k) :
    ((upperSlabEquiv K k).symm z).val =
      ((upperTruncatedExponentChamber K k 1).symm z.val.1, z.val.2) := by
  have h := coe_upperSlabEquiv K k ((upperSlabEquiv K k).symm z)
  simpa [Prod.map] using
    congrArg (Prod.map (upperTruncatedExponentChamber K k 1).symm id) h.symm

private def inverseUpperLeftGrade (q : ℤ × ℤ × ℤ) :
    truncatedExponentChamberGrade K k 1 q →ₗ[K]
      truncatedExponentChamberGrade K k 1 (upperExponent.symm q) :=
  (((upperTruncatedExponentChamber K k 1).symm.toLinearMap).comp
    (truncatedExponentChamberGrade K k 1 q).subtype).codRestrict _ fun u => by
      have he := upperTruncatedExponentChamber_mem_grade_iff K k 1
        (upperExponent.symm q) ((upperTruncatedExponentChamber K k 1).symm u.val)
      apply he.mp
      simpa only [← upperExponent_apply, LinearEquiv.apply_symm_apply,
        AlgEquiv.apply_symm_apply] using u.property

/-- The left incoming lift in the upper frame. Undo the exponent shear on the
source piece, lift to the lower slab, and pass to the upper gluing algebra. -/
def upperLeftChamberLift (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0}) :
    truncatedExponentChamberGrade K k 1 q.val →ₗ[K] upperSlabAlgebra τ k :=
  ((upperSlabEquiv K k).toLinearMap.restrictScalars K).comp
    ((leftChamberLift K k ⟨upperExponent.symm q.val, by
      simpa only [Set.mem_ofPred_eq, upperExponent_symm_apply] using
        (q.property : q.val.1 ≤ 0)⟩).comp
        (inverseUpperLeftGrade K k q.val))

/-- The right incoming lift in the upper presentation. The right chamber frame
and its exponent degree are unchanged. -/
def upperRightChamberLift (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1}) :
    truncatedExponentChamberGrade K k 0 q.val →ₗ[K] upperSlabAlgebra τ k :=
  ((upperSlabEquiv K k).toLinearMap.restrictScalars K).comp (rightChamberLift K k q)

/-- Evaluation of the upper left lift on a whole homogeneous coefficient. -/
theorem upperLeftChamberLift_apply (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    upperLeftChamberLift K k q u = upperSlabEquiv K k
      (leftChamberLift K k ⟨upperExponent.symm q.val, by
        simpa only [Set.mem_ofPred_eq, upperExponent_symm_apply] using
          (q.property : q.val.1 ≤ 0)⟩
          ⟨(upperTruncatedExponentChamber K k 1).symm u.val, by
            apply (upperTruncatedExponentChamber_mem_grade_iff K k 1
              (upperExponent.symm q.val) _).mp
            simpa only [← upperExponent_apply, LinearEquiv.apply_symm_apply,
              AlgEquiv.apply_symm_apply] using u.property⟩) := (rfl)

/-- Evaluation of the upper right lift. -/
@[simp]
theorem upperRightChamberLift_apply (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) :
    upperRightChamberLift K k q u = upperSlabEquiv K k (rightChamberLift K k q u) := (rfl)

/-- The left projection of an upper incoming lift recovers its entire source. -/
@[simp]
theorem upperLeftChamberLift_fst (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    (upperLeftChamberLift K k q u).val.1 = u.val := by
  rw [upperLeftChamberLift_apply, coe_upperSlabEquiv, leftChamberLift_fst]
  exact (upperTruncatedExponentChamber K k 1).apply_symm_apply u.val

/-- The upper gluing span with its canonical admissible homogeneous lifts.
The admissible horizontal half-spaces agree with those of the lower span. -/
def upperChamberCorrespondence :
    GradedCorrespondence (B := upperSlabAlgebra τ k)
      (truncatedExponentChamberGrade K k 1) (truncatedExponentChamberGrade K k 0)
      {q | q.1 ≤ 0} {q | 0 ≤ q.1} where
  left := ((AlgHom.fst R _ _).comp (upperSlabAlgebra τ k).val).toLinearMap.restrictScalars K
  right := ((AlgHom.snd R _ _).comp (upperSlabAlgebra τ k).val).toLinearMap.restrictScalars K
  liftLeft := upperLeftChamberLift K k
  liftRight := upperRightChamberLift K k
  left_liftLeft q := by ext u; exact upperLeftChamberLift_fst K k q u
  right_liftRight q := by ext u; simp

/-- The left leg is the actual upper fiber-product projection. -/
@[simp]
theorem upperChamberCorrespondence_left_apply (z : upperSlabAlgebra τ k) :
    (upperChamberCorrespondence K k).left z = z.val.1 := (rfl)

/-- The right leg is the actual upper fiber-product projection. -/
@[simp]
theorem upperChamberCorrespondence_right_apply (z : upperSlabAlgebra τ k) :
    (upperChamberCorrespondence K k).right z = z.val.2 := (rfl)

/-- The upper correspondence uses the canonical left incoming lift. -/
@[simp]
theorem upperChamberCorrespondence_liftLeft (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0}) :
    (upperChamberCorrespondence K k).liftLeft q = upperLeftChamberLift K k q := (rfl)

/-- The upper correspondence uses the canonical right incoming lift. -/
@[simp]
theorem upperChamberCorrespondence_liftRight (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1}) :
    (upperChamberCorrespondence K k).liftRight q = upperRightChamberLift K k q := (rfl)

/-- The two upper chamber projections are jointly injective. -/
theorem upperChamberCorrespondence_injective :
    Function.Injective ((upperChamberCorrespondence K k).left.prod
      (upperChamberCorrespondence K k).right) := by
  intro x y he
  exact Subtype.ext (Prod.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

/-- The gluing isomorphism carries each left incoming lift to the upper lift
at the sheared degree. No nonvanishing hypothesis on the piece is needed. -/
@[simp]
theorem upperSlabEquiv_leftChamberLift (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) :
    upperSlabEquiv K k (leftChamberLift K k q u) =
      upperLeftChamberLift K k ⟨upperExponent q.val, by
        simpa only [Set.mem_ofPred_eq, upperExponent_apply] using
          (q.property : q.val.1 ≤ 0)⟩
        ⟨upperTruncatedExponentChamber K k 1 u.val, by
          simpa only [upperExponent_apply] using
            (upperTruncatedExponentChamber_mem_grade_iff K k 1 q.val u.val).mpr u.property⟩ := by
  rw [upperLeftChamberLift_apply]
  simp only [AlgEquiv.symm_apply_apply]
  congr 1
  -- The lift's domain depends on its exponent, so compare the dependent functions
  -- and then their coefficient subtypes rather than unfolding either lift.
  apply congr_heq (congr_arg_heq
    (fun r : {r : ℤ × ℤ × ℤ | r.1 ≤ 0} =>
      fun v : truncatedExponentChamberGrade K k 1 r.val => leftChamberLift K k r v)
    (Subtype.ext (upperExponent.symm_apply_apply q.val).symm))
  exact (Subtype.heq_iff_coe_eq (fun x => by rw [LinearEquiv.symm_apply_apply])).mpr rfl

/-- The two crossing descriptions define lift-preserving correspondences,
with the upper exponent shear on the left and the identity on the right. -/
def upperChamberComparison :
    GradedCorrespondence.Hom (chamberCorrespondence K k) (upperChamberCorrespondence K k)
      upperExponent id where
  middle := (upperSlabEquiv K k).toLinearMap.restrictScalars K
  left := (upperTruncatedExponentChamber K k 1).toLinearMap
  right := LinearMap.id
  left_comm := by ext z; simp
  right_comm := by ext z; simp
  left_mem q x hx := by
    simpa only [AlgEquiv.toLinearMap_apply, upperExponent_apply] using
      (upperTruncatedExponentChamber_mem_grade_iff K k 1 q x).mpr hx
  right_mem _ _ hx := hx
  admissible_left q hq := by
    simpa only [Set.mem_ofPred_eq, upperExponent_apply] using (hq : q.1 ≤ 0)
  admissible_right _ hq := hq
  middle_liftLeft q u := by
    simpa only [chamberCorrespondence_liftLeft, upperChamberCorrespondence_liftLeft,
      LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply] using
      upperSlabEquiv_leftChamberLift K k q u
  middle_liftRight q u := by
    simp only [chamberCorrespondence_liftRight, upperChamberCorrespondence_liftRight,
      LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply,
      LinearMap.id_apply]
    rfl

/-- The middle comparison is the actual upper gluing isomorphism. -/
@[simp]
theorem upperChamberComparison_middle :
    (upperChamberComparison K k).middle =
      (upperSlabEquiv K k).toLinearMap.restrictScalars K := (rfl)

/-- The left comparison is the actual chamber shear. -/
@[simp]
theorem upperChamberComparison_left :
    (upperChamberComparison K k).left =
      (upperTruncatedExponentChamber K k 1).toLinearMap := (rfl)

/-- The right comparison fixes the chamber. -/
@[simp]
theorem upperChamberComparison_right :
    (upperChamberComparison K k).right = LinearMap.id := (rfl)

/-- Left-to-right transfers agree for the two crossing descriptions after
shearing the incoming left degree and coefficient. -/
theorem upperChamberCorrespondence_transfer (q : {q : ℤ × ℤ × ℤ | q.1 ≤ 0})
    (u : truncatedExponentChamberGrade K k 1 q.val) (η : ℤ × ℤ × ℤ) :
    ((upperChamberCorrespondence K k).transfer
      ⟨upperExponent q.val, (upperChamberComparison K k).admissible_left q.property⟩ η
      ⟨upperTruncatedExponentChamber K k 1 u.val,
        by simpa only [upperExponent_apply] using
          (upperTruncatedExponentChamber_mem_grade_iff K k 1 q.val u.val).mpr u.property⟩ :
          TruncatedExponentChamber K k 0) =
      ((chamberCorrespondence K k).transfer q η u : TruncatedExponentChamber K k 0) := by
  simpa only [upperChamberComparison_left, upperChamberComparison_right,
    AlgEquiv.toLinearMap_apply, LinearMap.id_apply, id_eq] using
    (upperChamberComparison K k).transfer_map_of_injective Function.injective_id q u η

/-- Right-to-left transfers agree after shearing the outgoing left degree
and its whole coefficient. The input degree on the right is unchanged. -/
theorem upperChamberCorrespondence_symm_transfer (q : {q : ℤ × ℤ × ℤ | 0 ≤ q.1})
    (u : truncatedExponentChamberGrade K k 0 q.val) (η : ℤ × ℤ × ℤ) :
    ((upperChamberCorrespondence K k).symm.transfer q (upperExponent η) u :
        TruncatedExponentChamber K k 1) =
      upperTruncatedExponentChamber K k 1
        ((chamberCorrespondence K k).symm.transfer q η u) := by
  simpa only [GradedCorrespondence.Hom.symm_left, GradedCorrespondence.Hom.symm_right,
    upperChamberComparison_left, upperChamberComparison_right,
    AlgEquiv.toLinearMap_apply, LinearMap.id_apply, id_eq] using
    (upperChamberComparison K k).symm.transfer_map_of_injective upperExponent.injective q u η

end Mei.FocusFocus
