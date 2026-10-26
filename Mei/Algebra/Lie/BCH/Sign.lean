/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Transition
public import Mei.Algebra.Lie.BCH.Subgroup

/-!
# Finite sign factorization in BCH groups

Every element of a finite positive-degree BCH truncation has unique positive,
zero and negative factors, in that order, for any additive ordered functional
on the grading indices. The factors commute with lowering the degree cutoff.
They are set-theoretic coordinates; multiplication of factors is not asserted
to be a homomorphism from the product group.

The proof lifts factorizations through the central truncation kernels, splitting
each logarithmic correction with `Mei.signDecomposition`. It uses the existing
`LieSubalgebra.bchSubgroup` and `PositiveDegrees.ker_truncationMap_succ_le_center`.
-/

public section

noncomputable section

namespace Mei

open BCHGroup

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

section Nilpotent

variable [LieRing.IsNilpotent L]
  (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ] (θ : N →+ A)

/-- Multiply sign factors in positive, zero, negative order. -/
def signProduct (a : ∀ s, (signSubalgebra ℒ θ s).bchSubgroup) : BCHGroup L :=
  (a 1 : BCHGroup L) * a 0 * a (-1)

/-- The positive factor is leftmost and the negative factor is rightmost. -/
@[simp]
theorem signProduct_apply (a : ∀ s, (signSubalgebra ℒ θ s).bchSubgroup) :
    signProduct ℒ θ a = (a 1 : BCHGroup L) * a 0 * a (-1) := (rfl)

private theorem signProduct_central_mul
    (a b : ∀ s, (signSubalgebra ℒ θ s).bchSubgroup)
    (ha : ∀ s, log (a s : BCHGroup L) ∈ LieAlgebra.center R L) :
    signProduct ℒ θ (fun s => a s * b s) =
      exp (∑ s, log (a s : BCHGroup L)) * signProduct ℒ θ b := by
  have hbracket (s : SignType) (x : L) : ⁅log (a s : BCHGroup L), x⁆ = 0 := by
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule R L L _).mp (ha s) x, neg_zero]
  have hc (s : SignType) (g : BCHGroup L) : Commute (a s : BCHGroup L) g := by
    rw [← exp_log (a s : BCHGroup L), ← exp_log g]
    exact commute_exp_of_lie_eq_zero _ _ (hbracket s _)
  have hs : ∑ s, log (a s : BCHGroup L) =
      log (a 1 : BCHGroup L) + log (a 0 : BCHGroup L) + log (a (-1) : BCHGroup L) := by
    simp [SignType.univ_eq]
    abel
  have hexp : exp (∑ s, log (a s : BCHGroup L)) =
      (a 1 : BCHGroup L) * a 0 * a (-1) := by
    rw [hs, exp_add_of_lie_eq_zero _ _ (by simp [add_lie, hbracket]),
      exp_add_of_lie_eq_zero _ _ (hbracket 1 _)]
    simp
  rw [hexp, signProduct_apply, signProduct_apply]
  simp only [Subgroup.coe_mul]
  calc
    _ = ((a 1 : BCHGroup L) * a 0) * (b 1 * b 0) * (a (-1) * b (-1)) := by
      rw [(hc 0 (b 1)).symm.mul_mul_mul_comm]
    _ = _ := by
      rw [(hc (-1) (b 1 * b 0)).symm.mul_mul_mul_comm]

end Nilpotent

namespace PositiveDegrees

variable [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] (θ : N →+ A)

/-- Multiplication gives a bijection from the three sign subgroups to every finite
positive-degree BCH truncation. No finite generation of the positive monoid is needed. -/
theorem signProduct_bijective (k : ℕ) :
    Function.Bijective (signProduct (d.truncatedGrading ℒ k) θ) := by
  induction k with
  | zero =>
    have hzero (x : d.truncatedLie ℒ 0) : x = 0 := by
      obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ 0).surjective_mkQ x
      exact (d.degreeIdeal ℒ 0).mkQ_eq_zero.mpr (by simp)
    have hone (g : BCHGroup (d.truncatedLie ℒ 0)) : g = 1 := by
      apply log_injective
      simpa using hzero (log g)
    constructor
    · intro a b _
      funext s
      exact Subtype.ext ((hone _).trans (hone _).symm)
    · intro g
      exact ⟨fun _ => 1, (hone _).trans (hone _).symm⟩
  | succ k ih =>
    let q := d.truncationMap ℒ (Nat.le_succ k)
    let K (s) := signSubalgebra (d.truncatedGrading ℒ (k + 1)) θ s
    let K₀ (s) := signSubalgebra (d.truncatedGrading ℒ k) θ s
    let lower (a : ∀ s, (K s).bchSubgroup) : ∀ s, (K₀ s).bchSubgroup :=
      fun s => ⟨q.bchGroupMap (a s), by
        dsimp only [K₀]
        rw [LieSubalgebra.mem_bchSubgroup,
          ← d.map_signSubalgebra_truncationMap ℒ θ (Nat.le_succ k) s]
        exact (LieSubalgebra.mem_map _ _ _).mpr
          ⟨log (a s), (LieSubalgebra.mem_bchSubgroup _ _).mp (a s).property,
            by simp [q]⟩⟩
    have hprod (a) : signProduct _ θ (lower a) =
        q.bchGroupMap (signProduct _ θ a) := by simp [lower]
    have hcenter {g : BCHGroup (d.truncatedLie ℒ (k + 1))}
        (hg : q.bchGroupMap g = 1) : log g ∈ LieAlgebra.center R _ := by
      apply d.ker_truncationMap_succ_le_center ℒ k
      exact LieHom.mem_ker.mpr (by simpa using congrArg log hg)
    constructor
    · -- Equal products give equal lower factors. Their differences are central,
      -- and uniqueness of the linear sign decomposition kills all differences.
      intro a b hab
      have hlower : lower a = lower b := ih.1 (by rw [hprod, hprod, hab])
      let c : ∀ s, (K s).bchSubgroup := fun s => a s * (b s)⁻¹
      have hc (s) : q.bchGroupMap (c s) = 1 := by
        have he := congrArg (fun f => (f s : BCHGroup (d.truncatedLie ℒ k))) hlower
        simpa [lower, c] using mul_inv_eq_one.mpr he
      have hsum : ∑ s, log (c s : BCHGroup (d.truncatedLie ℒ (k + 1))) = 0 := by
        have he := signProduct_central_mul (d.truncatedGrading ℒ (k + 1)) θ c b
          (fun s => hcenter (hc s))
        have hcb : (fun s => c s * b s) = a := by funext s; simp [c]
        rw [hcb, hab] at he
        have hexp : exp (∑ s, log (c s : BCHGroup (d.truncatedLie ℒ (k + 1)))) = 1 :=
          mul_right_cancel (he.symm.trans (one_mul _).symm)
        simpa using congrArg log hexp
      have hcomponents := (signDecomposition_eq_iff
        (d.truncatedGrading ℒ (k + 1)) θ 0
        (fun s => ⟨log (c s), (LieSubalgebra.mem_bchSubgroup _ _).mp (c s).property⟩)).mpr hsum
      funext s
      apply Subtype.ext
      apply mul_inv_eq_one.mp
      apply log_injective
      have he := congrArg Subtype.val (hcomponents s)
      simpa [c] using he.symm
    · -- Lift the lower factors, then split the central logarithmic error by sign.
      intro g
      obtain ⟨a₀, ha₀⟩ := ih.2 (q.bchGroupMap g)
      have hlift (s) : ∃ a : (K s).bchSubgroup,
          q.bchGroupMap a = (a₀ s : BCHGroup (d.truncatedLie ℒ k)) := by
        have he := congrArg LieSubalgebra.bchSubgroup
          (d.map_signSubalgebra_truncationMap ℒ θ (Nat.le_succ k) s)
        rw [LieSubalgebra.bchSubgroup_map] at he
        have hm : (a₀ s : BCHGroup (d.truncatedLie ℒ k)) ∈
            ((K s).bchSubgroup).map q.bchGroupMap := by
          simpa only [K, q, he] using (a₀ s).property
        obtain ⟨x, hx, hxe⟩ := hm
        exact ⟨⟨x, hx⟩, hxe⟩
      choose a ha using hlift
      have hlower : lower a = a₀ := by funext s; exact Subtype.ext (ha s)
      let z := log (g * (signProduct _ θ a)⁻¹)
      have hz : z ∈ q.ker := by
        apply LieHom.mem_ker.mpr
        have he : q.bchGroupMap (g * (signProduct _ θ a)⁻¹) = 1 := by
          rw [map_mul, map_inv, ← hprod, hlower, ha₀, mul_inv_cancel]
        simpa only [LieHom.log_bchGroupMap, log_one] using congrArg log he
      let v := signDecomposition (d.truncatedGrading ℒ (k + 1)) θ z
      have hv (s) : (v s : d.truncatedLie ℒ (k + 1)) ∈ q.ker :=
        signDecomposition_mem _ θ q.ker.toSubmodule
          (d.ker_truncationMap_isHomogeneous ℒ (Nat.le_succ k)) hz s
      let c : ∀ s, (K s).bchSubgroup := fun s => ⟨exp (v s : _), by simp⟩
      refine ⟨fun s => c s * a s, ?_⟩
      rw [signProduct_central_mul _ θ c a]
      · have he : ∑ s, log (c s : BCHGroup (d.truncatedLie ℒ (k + 1))) = z := by
          simp [c, v]
        rw [he]
        dsimp only [z]
        rw [exp_log, mul_assoc, inv_mul_cancel, mul_one]
      · intro s
        simpa [c] using d.ker_truncationMap_succ_le_center ℒ k (hv s)

/-- Exponential sign coordinates on a finite BCH truncation. The inverse multiplies
positive, zero and negative factors, in that order. -/
def signFactorization (k : ℕ) :
    BCHGroup (d.truncatedLie ℒ k) ≃
      ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup :=
  (Equiv.ofBijective _ (d.signProduct_bijective ℒ θ k)).symm

/-- Recombining finite sign coordinates is ordered multiplication. -/
@[simp]
theorem signFactorization_symm_apply (k : ℕ)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup) :
    (d.signFactorization ℒ θ k).symm a = signProduct _ θ a := (rfl)

/-- The factors of an element multiply back to that element. -/
@[simp]
theorem signProduct_signFactorization (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k)) :
    (d.signFactorization ℒ θ k g 1 : BCHGroup (d.truncatedLie ℒ k)) *
      d.signFactorization ℒ θ k g 0 * d.signFactorization ℒ θ k g (-1) = g := by
  simpa only [signFactorization_symm_apply, signProduct_apply] using
    (d.signFactorization ℒ θ k).symm_apply_apply g

/-- Taking sign coordinates of an ordered product recovers each prescribed factor. -/
@[simp]
theorem signFactorization_signProduct (k : ℕ)
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup) :
    d.signFactorization ℒ θ k ((a 1 : BCHGroup (d.truncatedLie ℒ k)) * a 0 * a (-1)) = a := by
  simpa only [signFactorization_symm_apply, signProduct_apply] using
    (d.signFactorization ℒ θ k).apply_symm_apply a

/-- A proposed family is the sign factorization exactly when it recombines to `g`. -/
theorem signFactorization_eq_iff (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (a : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup) :
    d.signFactorization ℒ θ k g = a ↔ signProduct _ θ a = g := by
  rw [← Equiv.eq_symm_apply, signFactorization_symm_apply]
  exact eq_comm

/-- Every sign factor of the identity is the identity. -/
@[simp]
theorem signFactorization_one (k : ℕ) :
    d.signFactorization ℒ θ k 1 = fun _ => 1 := by
  apply (d.signFactorization_eq_iff ℒ θ k 1 _).mpr
  simp

/-- Lowering the cutoff preserves each of the three sign factors. -/
@[simp]
theorem truncationMap_signFactorization {k l : ℕ} (h : k ≤ l)
    (g : BCHGroup (d.truncatedLie ℒ l)) (s : SignType) :
    (d.truncationMap ℒ h).bchGroupMap (d.signFactorization ℒ θ l g s) =
      (d.signFactorization ℒ θ k ((d.truncationMap ℒ h).bchGroupMap g) s :
        BCHGroup (d.truncatedLie ℒ k)) := by
  let a := d.signFactorization ℒ θ l g
  let b : ∀ s, (signSubalgebra (d.truncatedGrading ℒ k) θ s).bchSubgroup :=
    fun s => ⟨(d.truncationMap ℒ h).bchGroupMap (a s), by
      rw [LieSubalgebra.mem_bchSubgroup,
        ← d.map_signSubalgebra_truncationMap ℒ θ h s]
      exact (LieSubalgebra.mem_map _ _ _).mpr
        ⟨log (a s), (LieSubalgebra.mem_bchSubgroup _ _).mp (a s).property, by simp⟩⟩
  have he : d.signFactorization ℒ θ k ((d.truncationMap ℒ h).bchGroupMap g) = b := by
    apply (d.signFactorization_eq_iff ℒ θ k _ _).mpr
    have hg := congrArg (d.truncationMap ℒ h).bchGroupMap
      (d.signProduct_signFactorization ℒ θ l g)
    simpa only [signProduct_apply, map_mul] using hg
  exact (congrArg (fun f => (f s : BCHGroup (d.truncatedLie ℒ k))) he).symm

end PositiveDegrees
end Mei
