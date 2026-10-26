/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Coordinates
public import Mei.Data.Finset.NoncommProd

/-!
# Homogeneous factors of completed BCH labels

A completed BCH label has a homogeneous logarithmic coefficient in every degree, read
from its exponential coordinate in the degree completion. Exponentiating the degree-`n`
coefficient gives the homogeneous factor of degree `n`. At every cutoff only finitely
many of these factors are nontrivial. When the coefficients commute pairwise, the label
projects at every order to the unordered product of its projected factors, computed on
any finite set of degrees containing the nonzero coefficients up to that order.
Conversely, pairwise commuting homogeneous elements whose exponentials multiply to the
label at every order are its coefficients.

This splits a label whose logarithm is supported on an abelian family of degrees, such
as a supported ray with abelian ray Lie algebra, into labels of pure degree. The
coefficients are `Mei.PositiveDegrees.completionComponent` of the exponential
coordinate `Mei.PositiveDegrees.completedBCHExp`; the finite products are Mathlib's
`Finset.noncommProd`, related to finite sums by `Mei.BCHGroup.exp_sum_of_lie_eq_zero`.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- The degree-`n` coefficient of the exponential coordinate of a completed label. -/
def logComponent (g : d.completedBCHGroup ℒ) (n : N) : ℒ n :=
  d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n
    ((d.completedBCHExp ℒ).symm g)

/-- The homogeneous factor of degree `n`: the completed exponential of the degree-`n`
logarithmic coefficient. -/
def homogeneousFactor (g : d.completedBCHGroup ℒ) (n : N) : d.completedBCHGroup ℒ :=
  d.expToCompletion ℒ (d.logComponent ℒ g n)

/-- Unfold a homogeneous factor to the completed exponential of its coefficient. -/
theorem homogeneousFactor_def (g : d.completedBCHGroup ℒ) (n : N) :
    d.homogeneousFactor ℒ g n = d.expToCompletion ℒ (d.logComponent ℒ g n) := (rfl)

/-- At every order, a homogeneous factor is the exponential of the class of its coefficient. -/
@[simp]
theorem projection_homogeneousFactor (g : d.completedBCHGroup ℒ) (n : N) (k : ℕ) :
    CompletedGroup.projection k (d.homogeneousFactor ℒ g n) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ (d.logComponent ℒ g n)) :=
  d.projection_expToCompletion ℒ k _

/-- The coefficients of a completed exponential are the coefficients of its coordinate. -/
@[simp]
theorem logComponent_completedBCHExp (x : d.completedLie ℒ) (n : N) :
    d.logComponent ℒ (d.completedBCHExp ℒ x) n =
      d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n x := by
  rw [logComponent, Equiv.symm_apply_apply]

/-- At any cutoff retaining degree `n`, the coefficient is the homogeneous component of any
representative of the finite logarithm. -/
theorem logComponent_eq_decompose (g : d.completedBCHGroup ℒ) {n : N} {k : ℕ}
    (hn : d.degree n ≤ k) {x : L}
    (hx : (d.degreeIdeal ℒ k).mkQ x =
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g)) :
    d.logComponent ℒ g n = DirectSum.decompose ℒ x n := by
  rw [logComponent, completionComponent_eq_quotientComponent d ℒ F _ n k hn,
    ← LieIdeal.completionProjection_apply, completionProjection_completedBCHExp_symm, ← hx,
    LieIdeal.mkQ_apply]
  exact d.quotientComponent_mk ℒ F _ k n hn x

/-- The coefficients of the identity label vanish. -/
@[simp]
theorem logComponent_one (n : N) : d.logComponent ℒ 1 n = 0 := by
  rw [logComponent, completedBCHExp_symm_one, map_zero]

/-- Coefficients vanish in degrees carrying no homogeneous piece. -/
theorem logComponent_eq_zero_of_notMem_monoid (g : d.completedBCHGroup ℒ) {n : N}
    (hn : n ∉ d.monoid) : d.logComponent ℒ g n = 0 := by
  have hb : ℒ n = ⊥ := IsPositiveGrading.eq_bot n (Or.inl hn)
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  exact (Submodule.eq_bot_iff _).mp hb _ (d.logComponent ℒ g n).property

/-- A homogeneous factor above the cutoff projects trivially. -/
theorem projection_homogeneousFactor_of_lt (g : d.completedBCHGroup ℒ) {n : N} {k : ℕ}
    (hn : (k : ℤ) < d.degree n) :
    CompletedGroup.projection k (d.homogeneousFactor ℒ g n) = 1 := by
  rw [projection_homogeneousFactor,
    (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (d.le_degreeIdeal ℒ hn (d.logComponent ℒ g n).property)]
  exact BCHGroup.exp_zero

/-- A homogeneous factor projects trivially at order `k` unless its degree is retained
there and its coefficient is nonzero. -/
theorem projection_homogeneousFactor_eq_one (g : d.completedBCHGroup ℒ) {n : N} {k : ℕ}
    (h : d.degree n ≤ k → d.logComponent ℒ g n = 0) :
    CompletedGroup.projection k (d.homogeneousFactor ℒ g n) = 1 := by
  by_cases hn : d.degree n ≤ k
  · rw [homogeneousFactor_def, h hn, ZeroMemClass.coe_zero, expToCompletion_zero, map_one]
  · exact d.projection_homogeneousFactor_of_lt ℒ g (lt_of_not_ge hn)

/-- The homogeneous factors of a label have finite support at every order. -/
theorem hasFiniteSupport_homogeneousFactor (g : d.completedBCHGroup ℒ) :
    CompletedGroup.HasFiniteSupport (d.homogeneousFactor ℒ g) := by
  intro k
  apply (d.finite_cutoff k).subset
  intro n hn
  by_contra hc
  apply hn
  apply d.projection_homogeneousFactor_eq_one ℒ g
  intro hk
  exact d.logComponent_eq_zero_of_notMem_monoid ℒ g fun hP => hc (d.mem_cutoff.mpr ⟨hP, hk⟩)

/-- Homogeneous factors with commuting coefficients commute. -/
theorem commute_homogeneousFactor {g : d.completedBCHGroup ℒ} {n m : N}
    (h : ⁅(d.logComponent ℒ g n : L), (d.logComponent ℒ g m : L)⁆ = 0) :
    Commute (d.homogeneousFactor ℒ g n) (d.homogeneousFactor ℒ g m) :=
  d.commute_expToCompletion_of_lie_eq_zero ℒ h

/-- At order `k`, the finite logarithm is the class of the sum of the coefficients
retained at that order. -/
theorem log_projection_eq_mkQ_sum (g : d.completedBCHGroup ℒ) (k : ℕ) :
    BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) =
      (d.degreeIdeal ℒ k).mkQ
        (∑ n ∈ (d.finite_cutoff k).toFinset, (d.logComponent ℒ g n : L)) := by
  let e := d.completionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
    (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn))
  rw [← completionProjection_completedBCHExp_symm, LieIdeal.completionProjection_apply,
    ← e.symm_apply_apply ((d.completedBCHExp ℒ).symm g),
    projection_completionEquivPi_symm]
  simp only [e, completionEquivPi_apply, LieIdeal.mkQ_apply, logComponent]

variable {ℒ} in
/-- Pairwise commuting coefficients split a completed label at every order into the
unordered product of its homogeneous factors, over any finite set of degrees containing
every nonzero coefficient retained at that order. -/
theorem projection_eq_noncommProd_homogeneousFactor {g : d.completedBCHGroup ℒ}
    (hg : ∀ n m, ⁅(d.logComponent ℒ g n : L), (d.logComponent ℒ g m : L)⁆ = 0)
    (k : ℕ) (s : Finset N)
    (hs : ∀ n, d.degree n ≤ k → d.logComponent ℒ g n ≠ 0 → n ∈ s) :
    CompletedGroup.projection k g =
      s.noncommProd (fun n => CompletedGroup.projection k (d.homogeneousFactor ℒ g n))
        (fun n _ m _ _ => (d.commute_homogeneousFactor ℒ (hg n m)).map _) := by
  classical
  let c := (d.finite_cutoff k).toFinset
  let f n := CompletedGroup.projection k (d.homogeneousFactor ℒ g n)
  have hcomm (t : Finset N) : (t : Set N).Pairwise fun a b => Commute (f a) (f b) :=
    fun n _ m _ _ => (d.commute_homogeneousFactor ℒ (hg n m)).map _
  have hc : CompletedGroup.projection k g = c.noncommProd f (hcomm c) := by
    rw [← BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
      log_projection_eq_mkQ_sum, map_sum,
      BCHGroup.exp_sum_of_lie_eq_zero c _ fun n _ m _ _ => by
        beta_reduce
        rw [← LieHom.map_lie, hg n m, map_zero]]
    exact Finset.noncommProd_congr rfl (fun n _ => (d.projection_expToCompletion ℒ k _).symm) _
  have hcs := Finset.noncommProd_subset (Finset.subset_union_left (s₂ := s)) f
    (hcomm (c ∪ s)) fun n _ hn => d.projection_homogeneousFactor_eq_one ℒ g fun hk =>
      d.logComponent_eq_zero_of_notMem_monoid ℒ g fun hP =>
        hn ((d.finite_cutoff k).mem_toFinset.mpr (d.mem_cutoff.mpr ⟨hP, hk⟩))
  have hsc := Finset.noncommProd_subset (Finset.subset_union_right (s₁ := c)) f
    (hcomm (c ∪ s)) fun n _ hn => d.projection_homogeneousFactor_eq_one ℒ g fun hk => by
      by_contra h0
      exact hn (hs n hk h0)
  exact hc.trans (hcs.trans hsc.symm)

variable {ℒ} in
/-- Pairwise commuting homogeneous elements whose exponentials multiply to a completed
label at every order are its logarithmic coefficients. -/
theorem logComponent_eq_of_projection_eq_noncommProd {g : d.completedBCHGroup ℒ}
    (x : ∀ n, ℒ n) (hx : ∀ n m, ⁅(x n : L), (x m : L)⁆ = 0)
    (h : ∀ k, CompletedGroup.projection k g =
      (d.finite_cutoff k).toFinset.noncommProd
        (fun n => CompletedGroup.projection k (d.expToCompletion ℒ (x n)))
        (fun n _ m _ _ => (d.commute_expToCompletion_of_lie_eq_zero ℒ (hx n m)).map _))
    (n : N) : d.logComponent ℒ g n = x n := by
  by_cases hP : n ∈ d.monoid
  · let k := (d.degree n).toNat
    have hk : d.degree n ≤ k := Int.self_le_toNat _
    have hg : CompletedGroup.projection k g = BCHGroup.exp
        ((d.degreeIdeal ℒ k).mkQ (∑ m ∈ (d.finite_cutoff k).toFinset, (x m : L))) := by
      rw [h k, map_sum, BCHGroup.exp_sum_of_lie_eq_zero _ _ fun a _ b _ _ => by
        beta_reduce
        rw [← LieHom.map_lie, hx a b, map_zero]]
      exact Finset.noncommProd_congr rfl (fun n _ => d.projection_expToCompletion ℒ k _) _
    have hlog : (d.degreeIdeal ℒ k).mkQ (∑ m ∈ (d.finite_cutoff k).toFinset, (x m : L)) =
        BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) := by
      rw [hg, BCHGroup.log_exp]
    rw [d.logComponent_eq_decompose ℒ g hk hlog, DirectSum.decompose_sum]
    apply Subtype.ext
    rw [DirectSum.sum_apply, Submodule.coe_sum,
      Finset.sum_eq_single_of_mem n
        ((d.finite_cutoff k).mem_toFinset.mpr (d.mem_cutoff.mpr ⟨hP, hk⟩))]
    · exact DirectSum.decompose_of_mem_same ℒ (x n).property
    · intro m _ hmn
      exact DirectSum.decompose_of_mem_ne ℒ (x m).property hmn
  · have hb : ℒ n = ⊥ := IsPositiveGrading.eq_bot n (Or.inl hP)
    apply Subtype.ext
    have h0 (y : ℒ n) : (y : L) = 0 := by simpa only [hb, Submodule.mem_bot] using y.property
    exact (h0 _).trans (h0 _).symm

end Mei.PositiveDegrees
