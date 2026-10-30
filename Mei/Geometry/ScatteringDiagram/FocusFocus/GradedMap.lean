/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Grading
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Naturality
public import Mei.RingTheory.GradedAlgebra.RingHom

/-!
# Graded reductions of the focus-focus chambers

Coefficient change and cutoff reduction preserve the full exponent grading on
both presentations of a focus-focus chamber. We bundle the existing reductions
as `GradedRingHom`s, so Mathlib's `map_directSumDecompose` computes their effect
on entire homogeneous components, even when specialization kills coefficients.
The induced maps on pieces are functorial, and on retained rank-one pieces they
are exactly the original coefficient homomorphism.

These maps supply the homogeneous coefficient reductions used in comparisons of
slab transfers at different cutoffs. Surjective coefficient maps remain surjective
on each piece, including degrees removed by the target cutoff.

We use `exponentOrderMap`, `truncatedExponentChamberMap` and the chamber dictionary,
Mathlib's graded ring homomorphisms, and Tau Ceti's homogeneous quotient pieces.
The chamber coordinates follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open AddMonoidAlgebra

variable {K K' K'' : Type*} [CommRing K] [CommRing K'] [CommRing K'']
  {k l m : ℕ} (φ : K →+* K') (hl : l ≤ k) (i : Fin 2)

/-- Coefficient change and cutoff reduction as a map of full exponent gradings
on the absolute chamber quotients. -/
def exponentOrderGradedMap :
    exponentOrderGrade K k i →+*ᵍ exponentOrderGrade K' l i where
  __ := exponentOrderMap φ hl i
  map_mem := by
    intro q x hx
    rw [exponentOrderGrade_def] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp hx
    rw [exponentOrderMap_mk]
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    exact mapAlgHom_mem_gradeBy φ.toNatAlgHom ha

/-- Forgetting the grading recovers the original absolute chamber reduction. -/
@[simp]
theorem exponentOrderGradedMap_toRingHom :
    (exponentOrderGradedMap φ hl i).toRingHom = exponentOrderMap φ hl i := (rfl)

/-- The graded reduction with unchanged coefficients and cutoff is the identity. -/
@[simp]
theorem exponentOrderGradedMap_id :
    exponentOrderGradedMap (RingHom.id K) (k := k) le_rfl i =
      GradedRingHom.id (exponentOrderGrade K k i) := by
  apply GradedRingHom.toRingHom_injective
  exact exponentOrderMap_id i

/-- Successive graded absolute chamber reductions compose. -/
theorem exponentOrderGradedMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (exponentOrderGradedMap ψ hm i).comp (exponentOrderGradedMap φ hl i) =
      exponentOrderGradedMap (ψ.comp φ) (hm.trans hl) i := by
  apply GradedRingHom.toRingHom_injective
  exact exponentOrderMap_comp φ hl i ψ hm

/-- Coefficient change and cutoff reduction as a map of the nodal chamber's
full exponent grading over the original coefficient ring. -/
def truncatedExponentChamberGradedMap :
    truncatedExponentChamberGrade K k i →+*ᵍ truncatedExponentChamberGrade K' l i where
  __ := truncatedExponentChamberMap φ hl i
  map_mem := by
    intro q x hx
    rw [mem_truncatedExponentChamberGrade_iff] at hx ⊢
    rw [truncatedExponentChamberEquiv_symm_map]
    exact (exponentOrderGradedMap φ hl i).map_mem hx

/-- Forgetting the grading recovers the nodal chamber reduction. -/
@[simp]
theorem truncatedExponentChamberGradedMap_toRingHom :
    (truncatedExponentChamberGradedMap φ hl i).toRingHom =
      truncatedExponentChamberMap φ hl i := (rfl)

/-- The graded nodal chamber reduction with unchanged data is the identity. -/
@[simp]
theorem truncatedExponentChamberGradedMap_id :
    truncatedExponentChamberGradedMap (RingHom.id K) (k := k) le_rfl i =
      GradedRingHom.id (truncatedExponentChamberGrade K k i) := by
  apply GradedRingHom.toRingHom_injective
  exact truncatedExponentChamberMap_id i

/-- Successive graded nodal chamber reductions compose. -/
theorem truncatedExponentChamberGradedMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (truncatedExponentChamberGradedMap ψ hm i).comp
        (truncatedExponentChamberGradedMap φ hl i) =
      truncatedExponentChamberGradedMap (ψ.comp φ) (hm.trans hl) i := by
  apply GradedRingHom.toRingHom_injective
  exact truncatedExponentChamberMap_comp φ hl i ψ hm

/-- On a retained rank-one piece, the graded reduction applies precisely the
coefficient homomorphism to its scalar coordinate. -/
@[simp]
theorem exponentOrderGradedMap_gradeEquiv (q : exponentMonoid)
    (hq : chamberOrder i q ≤ l) (r : K) :
    (exponentOrderGradedMap φ hl i).gradedAddHom q.val
        (exponentOrderGradeEquiv K k i q (hq.trans hl) r) =
      exponentOrderGradeEquiv K' l i q hq (φ r) := by
  apply Subtype.ext
  simp only [GradedRingHom.gradedAddHom_apply_coe, coe_exponentOrderGradeEquiv_apply,
    ← GradedRingHom.coe_toRingHom, exponentOrderGradedMap_toRingHom,
    exponentOrderMap_mk, mapRingHom_single]

/-- Every homogeneous target coefficient has a homogeneous preimage under an
absolute chamber reduction with surjective coefficient map. -/
theorem exponentOrderGradedMap_gradedAddHom_surjective (hφ : Function.Surjective φ)
    (q : ℤ × ℤ × ℤ) :
    Function.Surjective ((exponentOrderGradedMap φ hl i).gradedAddHom q) :=
  (exponentOrderGradedMap φ hl i).gradedAddHom_surjective
    (exponentOrderMap_surjective φ hl i hφ) q

/-- Surjective coefficient changes also lift every homogeneous nodal chamber
coefficient, without a retained-degree or nonzero-coefficient hypothesis. -/
theorem truncatedExponentChamberGradedMap_gradedAddHom_surjective
    (hφ : Function.Surjective φ) (q : ℤ × ℤ × ℤ) :
    Function.Surjective ((truncatedExponentChamberGradedMap φ hl i).gradedAddHom q) :=
  (truncatedExponentChamberGradedMap φ hl i).gradedAddHom_surjective
    (truncatedExponentChamberMap_surjective φ hl i hφ) q

end Mei.FocusFocus
