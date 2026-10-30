/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Upper.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Overlap

/-!
# Upper gluing of the focus-focus chambers

The upper shear of a chamber descends to the upper change on its doubly
truncated overlap. Consequently the lower left incidence equals the upper
wall incidence after shearing the left chamber. The right chamber stays in
its original frame. These equations identify the fiber products defined by
the two crossing descriptions, including their actual chamber projections.

The construction uses `upperTruncatedExponentChamber`, `upperOverlap` and
`lowerWallMap_eq_upperWallMap_comp_upperOverlap`, with Mathlib's equalizer
subalgebras and `AlgEquiv.subalgebraMap`. The coordinate and gluing conventions
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
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

end Mei.FocusFocus
