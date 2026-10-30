/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Comparison
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Decorated

/-!
# Realizing full chamber transfers by decorated slab rays

A surviving full exponent component of a truncated chamber crossing, whose
crossing height is nonzero and whose endpoint lies on the opposite side
(`Q.1 / (q.val.1 : ℝ) < 0`), determines exactly one decorated slab ray in the
Laurent presentation. The equivalence retains the smoothing exponent in the
chamber degree and absorbs its power into the Laurent coefficient. It preserves
the entire decoration, including torsion and nilpotent coefficients. Both
crossing directions use the existing geometric rays, including their upper-chart
incoming germs; no new path carrier is introduced.

The constructions use `chamberCorrespondence_transfer_ne_zero_iff`, its reverse
crossing version, the faithful chamber Laurent realizations, and
`slabBrokenLineEquiv`. The slab coordinates follow Gross–Siebert,
*An Invitation to Toric Degenerations*, §2.2–2.3 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open scoped Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "ι" => AdjoinRoot.of (Polynomial.X ^ (k + 1) : Polynomial K)

/-- Surviving left-to-right full exponent components satisfying the nonsingular
crossing-height condition. Ray realization additionally requires an opposite endpoint. -/
abbrev LeftChamberRayDegree (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (Q : ℝ × ℝ) :=
  {η : ℤ × ℤ × ℤ //
    (chamberCorrespondence K k).transfer ⟨q.val, hq⟩ η
      ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ∧
      Q.2 - (η.2.1 : ℝ) * Q.1 / q.val.1 ≠ 0}

/-- Surviving right-to-left full exponent components with nonzero crossing height.
Ray realization additionally requires an opposite endpoint. -/
abbrev RightChamberRayDegree (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (Q : ℝ × ℝ) :=
  {η : ℤ × ℤ × ℤ //
    (chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ η
      ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
        (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ∧
      Q.2 - (η.2.1 : ℝ) * Q.1 / q.val.1 ≠ 0}

private theorem leftChamberBranch_image (q : exponentMonoid) (hq : q.val.1 ≤ 0)
    (c : K) (Q : ℝ × ℝ) :
    (fun j : Fin (q.val.1.natAbs + 1) => (q + tangentDegree j.val).val) ''
      {j | (ι c * τ ^ leftOrder q) * τ ^ q.val.1.natAbs *
        (q.val.1.natAbs.choose j.val : S) ≠ 0 ∧
          Q.2 - ((q.val.2.1 + j.val : ℤ) : ℝ) * Q.1 / q.val.1 ≠ 0} =
      {η | (chamberCorrespondence K k).transfer ⟨q.val, hq⟩ η
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ∧
            Q.2 - (η.2.1 : ℝ) * Q.1 / q.val.1 ≠ 0} := by
  ext η
  constructor
  · rintro ⟨j, ⟨hc, hh⟩, rfl⟩
    exact ⟨(chamberCorrespondence_transfer_single_ne_zero_iff_laurent K k q hq c j.val).mpr hc, by
      simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add]
        using hh⟩
  · rintro ⟨hη, hh⟩
    obtain ⟨j, hj, he, _, _⟩ :=
      (chamberCorrespondence_transfer_ne_zero_iff K k q hq c η).mp hη
    have hj' : j < q.val.1.natAbs + 1 := by omega
    refine ⟨⟨j, hj'⟩, ⟨?_, ?_⟩, he.symm⟩
    · apply (chamberCorrespondence_transfer_single_ne_zero_iff_laurent K k q hq c j).mp
      rw [← he]
      exact hη
    · rw [he] at hh
      simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add]
        using hh

private def leftChamberBranchEquiv (q : exponentMonoid) (hq : q.val.1 ≤ 0)
    (c : K) (Q : ℝ × ℝ) :
    SlabBranchIndex τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q ≃
      LeftChamberRayDegree K k q hq c Q :=
  (Equiv.Set.image (fun j : Fin (q.val.1.natAbs + 1) => (q + tangentDegree j.val).val) _
    (by
      intro a b he
      apply Fin.ext
      have ht := congrArg (fun η : ℤ × ℤ × ℤ => η.2.1) he
      simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add] at ht
      exact Int.ofNat_inj.mp (add_left_cancel ht))).trans
    (Set.equivOfEq (leftChamberBranch_image K k q hq c Q))

private theorem rightChamberBranch_image (q : exponentMonoid) (hq : 0 ≤ q.val.1)
    (c : K) (Q : ℝ × ℝ) :
    (fun j : Fin (q.val.1.natAbs + 1) => (q + tangentDegree j.val).val) ''
      {j | (ι c * τ ^ rightOrder q) * τ ^ q.val.1.natAbs *
        (q.val.1.natAbs.choose j.val : S) ≠ 0 ∧
          Q.2 - ((q.val.2.1 + j.val : ℤ) : ℝ) * Q.1 / q.val.1 ≠ 0} =
      {η | (chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ η
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩ ≠ 0 ∧
            Q.2 - (η.2.1 : ℝ) * Q.1 / q.val.1 ≠ 0} := by
  ext η
  constructor
  · rintro ⟨j, ⟨hc, hh⟩, rfl⟩
    exact ⟨(chamberCorrespondence_symm_transfer_single_ne_zero_iff_laurent
      K k q hq c j.val).mpr hc, by
      simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add]
        using hh⟩
  · rintro ⟨hη, hh⟩
    obtain ⟨j, hj, he, _, _⟩ :=
      (chamberCorrespondence_symm_transfer_ne_zero_iff K k q hq c η).mp hη
    have hj' : j < q.val.1.natAbs + 1 := by omega
    refine ⟨⟨j, hj'⟩, ⟨?_, ?_⟩, he.symm⟩
    · apply (chamberCorrespondence_symm_transfer_single_ne_zero_iff_laurent K k q hq c j).mp
      rw [← he]
      exact hη
    · rw [he] at hh
      simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add]
        using hh

private def rightChamberBranchEquiv (q : exponentMonoid) (hq : 0 ≤ q.val.1)
    (c : K) (Q : ℝ × ℝ) :
    SlabBranchIndex τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q ≃
      RightChamberRayDegree K k q hq c Q :=
  (Equiv.Set.image (fun j : Fin (q.val.1.natAbs + 1) => (q + tangentDegree j.val).val) _
    (by
      intro a b he
      apply Fin.ext
      have ht := congrArg (fun η : ℤ × ℤ × ℤ => η.2.1) he
      simp only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.snd_add, Prod.fst_add] at ht
      exact Int.ofNat_inj.mp (add_left_cancel ht))).trans
    (Set.equivOfEq (rightChamberBranch_image K k q hq c Q))

/-- Full left-to-right chamber components correspond to the actual Laurent slab
rays at an opposite endpoint. A killed component contributes no ray. -/
def leftChamberRayEquiv (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0) :
    LeftChamberRayDegree K k q hq c Q ≃
      SlabBrokenLine τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q :=
  (leftChamberBranchEquiv K k q hq c Q).symm.trans
    (slabBrokenLineEquiv τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q hQ)

/-- The analogous realization of right-to-left chamber components, with the
right incoming order absorbed into the scalar coefficient. -/
def rightChamberRayEquiv (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0) :
    RightChamberRayDegree K k q hq c Q ≃
      SlabBrokenLine τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q :=
  (rightChamberBranchEquiv K k q hq c Q).symm.trans
    (slabBrokenLineEquiv τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q hQ)

private theorem leftChamberBranchEquiv_val (q : exponentMonoid) (hq : q.val.1 ≤ 0)
    (c : K) (Q : ℝ × ℝ)
    (j : SlabBranchIndex τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q) :
    (leftChamberBranchEquiv K k q hq c Q j).val = (q + tangentDegree j.val.val).val := by
  -- The image and equal-set equivalences preserve the underlying degree.
  rfl

private theorem leftChamberRayEquiv_apply_branch (q : exponentMonoid) (hq : q.val.1 ≤ 0)
    (c : K) (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (j : SlabBranchIndex τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q) :
    leftChamberRayEquiv K k q hq c Q hQ (leftChamberBranchEquiv K k q hq c Q j) =
      slabBrokenLine τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q hQ j := by
  simp only [leftChamberRayEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    slabBrokenLineEquiv_apply]

/-- Recover the full chamber degree from the geometric ray: its smoothing
coordinate is the original one, and its tangential coordinate is the ray's. -/
@[simp]
theorem leftChamberRayEquiv_symm_val (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (β : SlabBrokenLine τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q) :
    ((leftChamberRayEquiv K k q hq c Q hQ).symm β).val =
      (q.val.1, β.degree.2, q.val.2.2) := by
  let e := slabBrokenLineEquiv τ (ι c * τ ^ leftOrder q)
    q.val.1 q.val.2.1 Q hQ
  have hb := congrArg (fun δ : SlabBrokenLine τ (ι c * τ ^ leftOrder q)
    q.val.1 q.val.2.1 Q => δ.degree.2) (e.apply_symm_apply β)
  rw [slabBrokenLineEquiv_apply, degree_slabBrokenLine] at hb
  -- Composition of the standard equivalences computes the inverse on underlying degrees.
  have hv : ((leftChamberRayEquiv K k q hq c Q hQ).symm β).val =
      (leftChamberBranchEquiv K k q hq c Q (e.symm β)).val := (rfl)
  refine hv.trans ((leftChamberBranchEquiv_val K k q hq c Q (e.symm β)).trans ?_)
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.fst_add,
        Prod.snd_add] using hb
    · simp

private theorem rightChamberBranchEquiv_val (q : exponentMonoid) (hq : 0 ≤ q.val.1)
    (c : K) (Q : ℝ × ℝ)
    (j : SlabBranchIndex τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q) :
    (rightChamberBranchEquiv K k q hq c Q j).val = (q + tangentDegree j.val.val).val := by
  -- The image and equal-set equivalences preserve the underlying degree.
  rfl

private theorem rightChamberRayEquiv_apply_branch (q : exponentMonoid) (hq : 0 ≤ q.val.1)
    (c : K) (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (j : SlabBranchIndex τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q) :
    rightChamberRayEquiv K k q hq c Q hQ (rightChamberBranchEquiv K k q hq c Q j) =
      slabBrokenLine τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q hQ j := by
  simp only [rightChamberRayEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    slabBrokenLineEquiv_apply]

/-- Recover the full chamber degree from the geometric ray: its smoothing
coordinate is the original one, and its tangential coordinate is the ray's. -/
@[simp]
theorem rightChamberRayEquiv_symm_val (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (β : SlabBrokenLine τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q) :
    ((rightChamberRayEquiv K k q hq c Q hQ).symm β).val =
      (q.val.1, β.degree.2, q.val.2.2) := by
  let e := slabBrokenLineEquiv τ (ι c * τ ^ rightOrder q)
    q.val.1 q.val.2.1 Q hQ
  have hb := congrArg (fun δ : SlabBrokenLine τ (ι c * τ ^ rightOrder q)
    q.val.1 q.val.2.1 Q => δ.degree.2) (e.apply_symm_apply β)
  rw [slabBrokenLineEquiv_apply, degree_slabBrokenLine] at hb
  -- Composition of the standard equivalences computes the inverse on underlying degrees.
  have hv : ((rightChamberRayEquiv K k q hq c Q hQ).symm β).val =
      (rightChamberBranchEquiv K k q hq c Q (e.symm β)).val := (rfl)
  refine hv.trans ((rightChamberBranchEquiv_val K k q hq c Q (e.symm β)).trans ?_)
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simpa only [AddSubmonoid.coe_add, coe_tangentDegree, Prod.fst_add,
        Prod.snd_add] using hb
    · simp

private theorem leftChamberBranch_decoration (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (j : SlabBranchIndex τ (ι c * τ ^ leftOrder q) q.val.1 q.val.2.1 Q) :
    rightChamberExponentMap K k
      ((chamberCorrespondence K k).transfer ⟨q.val, hq⟩
        (leftChamberBranchEquiv K k q hq c Q j).val
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩) =
      (slabBrokenLine τ (ι c * τ ^ leftOrder q)
        q.val.1 q.val.2.1 Q hQ j).decoration := by
  rw [leftChamberBranchEquiv_val,
    rightChamberExponentMap_transfer_single,
    decoration_slabBrokenLine]
  congr 1
  apply Prod.ext
  · have h := Int.natAbs_of_nonneg (neg_nonneg.mpr hq)
    rw [Int.natAbs_neg] at h
    omega
  · rfl

/-- Realization preserves the entire homogeneous decoration under the faithful
Laurent chamber map, including nilpotent smoothing powers and torsion coefficients. -/
theorem leftChamberRayEquiv_decoration (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (η : LeftChamberRayDegree K k q hq c Q) :
    rightChamberExponentMap K k
      ((chamberCorrespondence K k).transfer ⟨q.val, hq⟩ η.val
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩) =
      (leftChamberRayEquiv K k q hq c Q hQ η).decoration := by
  -- Specifying the predicate avoids unfolding the chamber quotient instances.
  exact (Equiv.forall_congr_right
    (q := fun η : LeftChamberRayDegree K k q hq c Q =>
      rightChamberExponentMap K k
      ((chamberCorrespondence K k).transfer ⟨q.val, hq⟩ η.val
        ⟨truncatedExponentChamberEquiv K k 1 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 1 q _).mpr ⟨c, rfl⟩⟩) =
      (leftChamberRayEquiv K k q hq c Q hQ η).decoration)
    (leftChamberBranchEquiv K k q hq c Q)).mp
      (fun j => (leftChamberBranch_decoration K k q hq c Q hQ j).trans
        (congrArg SlabBrokenLine.decoration
          (leftChamberRayEquiv_apply_branch K k q hq c Q hQ j)).symm) η

private theorem rightChamberBranch_decoration (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (j : SlabBranchIndex τ (ι c * τ ^ rightOrder q) q.val.1 q.val.2.1 Q) :
    leftChamberExponentMap K k
      ((chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩
        (rightChamberBranchEquiv K k q hq c Q j).val
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩) =
      (slabBrokenLine τ (ι c * τ ^ rightOrder q)
        q.val.1 q.val.2.1 Q hQ j).decoration := by
  rw [rightChamberBranchEquiv_val,
    leftChamberExponentMap_symm_transfer_single,
    decoration_slabBrokenLine]
  congr 1
  exact congrArg (fun a => (a, q.val.2.1 + j.val.val))
    (congrArg Neg.neg (Int.natAbs_of_nonneg hq).symm)

/-- Realization preserves the entire homogeneous decoration under the faithful
Laurent chamber map, including nilpotent smoothing powers and torsion coefficients. -/
theorem rightChamberRayEquiv_decoration (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K)
    (Q : ℝ × ℝ) (hQ : Q.1 / (q.val.1 : ℝ) < 0)
    (η : RightChamberRayDegree K k q hq c Q) :
    leftChamberExponentMap K k
      ((chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ η.val
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩) =
      (rightChamberRayEquiv K k q hq c Q hQ η).decoration := by
  -- Specifying the predicate avoids unfolding the chamber quotient instances.
  exact (Equiv.forall_congr_right
    (q := fun η : RightChamberRayDegree K k q hq c Q =>
      leftChamberExponentMap K k
      ((chamberCorrespondence K k).symm.transfer ⟨q.val, hq⟩ η.val
        ⟨truncatedExponentChamberEquiv K k 0 (Ideal.Quotient.mk _ (single q c)),
          (mem_truncatedExponentChamberGrade_iff_exists K k 0 q _).mpr ⟨c, rfl⟩⟩) =
      (rightChamberRayEquiv K k q hq c Q hQ η).decoration)
    (rightChamberBranchEquiv K k q hq c Q)).mp
      (fun j => (rightChamberBranch_decoration K k q hq c Q hQ j).trans
        (congrArg SlabBrokenLine.decoration
          (rightChamberRayEquiv_apply_branch K k q hq c Q hQ j)).symm) η

/-- Only finitely many full chamber degrees contribute at an endpoint, even
over an infinite coefficient ring. -/
instance (q : exponentMonoid) (hq : q.val.1 ≤ 0) (c : K) (Q : ℝ × ℝ) :
    Finite (LeftChamberRayDegree K k q hq c Q) :=
  Finite.of_equiv _ (leftChamberBranchEquiv K k q hq c Q)

/-- Only finitely many full chamber degrees contribute at an endpoint, even
over an infinite coefficient ring. -/
instance (q : exponentMonoid) (hq : 0 ≤ q.val.1) (c : K) (Q : ℝ × ℝ) :
    Finite (RightChamberRayDegree K k q hq c Q) :=
  Finite.of_equiv _ (rightChamberBranchEquiv K k q hq c Q)

end Mei.FocusFocus
