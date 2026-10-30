/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Coordinates
public import Mei.Algebra.Lie.BCH.Filtration
public import Mei.Data.Finset.NoncommProd

/-!
# Homogeneous factors of completed BCH labels

A completed BCH label has a homogeneous logarithmic coefficient in every degree, read
from its exponential coordinate in the degree completion, and these coefficients determine
the label. Labels whose coefficients commute pairwise commute. Exponentiating the degree-`n`
coefficient gives the homogeneous factor of degree `n`. At every cutoff only finitely
many of these factors are nontrivial. When the coefficients commute pairwise, the label
projects at every order to the unordered product of its projected factors, computed on
any finite set of degrees containing the nonzero coefficients up to that order.
Conversely, pairwise commuting homogeneous elements whose exponentials multiply to the
label at every order are its coefficients.

This splits a label whose logarithm is supported on an abelian family of degrees, such
as a supported ray with abelian ray Lie algebra, into labels of pure degree.

A label lies in the degree filtration above order `a` exactly when its coefficients vanish in
degrees at most `a`. On that filtration term the coefficients in degrees at most `2a + 1` add
under multiplication and are invariant under conjugation. Consequently, removing from a finite
product the factors lying in the filtration term changes the coefficients in degrees at most
`a + 1` by the sum of theirs, whatever the remaining factors are.

The coefficients are `Mei.PositiveDegrees.completionComponent` of the exponential
coordinate `Mei.PositiveDegrees.completedBCHExp`; the finite products are Mathlib's
`Finset.noncommProd`, related to finite sums by `Mei.BCHGroup.exp_sum_of_lie_eq_zero`. The
filtration statements use the commutator bound
`Mei.PositiveDegrees.commutator_top_degreeFiltration_le`.
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

/-- A completed label is determined by its logarithmic coefficients. -/
theorem ext_logComponent {g g' : d.completedBCHGroup ℒ}
    (h : ∀ n, d.logComponent ℒ g n = d.logComponent ℒ g' n) : g = g' := by
  apply (d.completedBCHExp ℒ).symm.injective
  apply (d.completionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
    (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn))).injective
  funext n
  simpa only [completionEquivPi_apply, logComponent] using h n

/-- The logarithmic coefficients of a completed exponential are the homogeneous
components of the original Lie element. -/
@[simp]
theorem logComponent_expToCompletion (x : L) (n : N) :
    d.logComponent ℒ (d.expToCompletion ℒ x) n = DirectSum.decompose ℒ x n := by
  apply d.logComponent_eq_decompose ℒ _ (Int.self_le_toNat (d.degree n))
  rw [projection_expToCompletion, BCHGroup.log_exp]

/-- A homogeneous factor retains the original logarithmic coefficient in its degree. -/
@[simp]
theorem logComponent_homogeneousFactor_same (g : d.completedBCHGroup ℒ) (n : N) :
    d.logComponent ℒ (d.homogeneousFactor ℒ g n) n = d.logComponent ℒ g n := by
  rw [homogeneousFactor_def, logComponent_expToCompletion]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same ℒ (d.logComponent ℒ g n).property

/-- A homogeneous factor has zero logarithmic coefficient in every other degree. -/
@[simp]
theorem logComponent_homogeneousFactor_of_ne (g : d.completedBCHGroup ℒ) {n m : N}
    (hnm : n ≠ m) : d.logComponent ℒ (d.homogeneousFactor ℒ g n) m = 0 := by
  rw [homogeneousFactor_def, logComponent_expToCompletion]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne ℒ (d.logComponent ℒ g n).property hnm

/-- The coefficients of the identity label vanish. -/
@[simp]
theorem logComponent_one (n : N) : d.logComponent ℒ 1 n = 0 := by
  rw [logComponent, completedBCHExp_symm_one, map_zero]

/-- Inverting a completed label negates each logarithmic coefficient. -/
@[simp]
theorem logComponent_inv (g : d.completedBCHGroup ℒ) (n : N) :
    d.logComponent ℒ g⁻¹ n = -d.logComponent ℒ g n := by
  rw [logComponent, completedBCHExp_symm_inv, map_neg, logComponent]

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
/-- Completed labels commute when all their logarithmic coefficients do. -/
theorem commute_of_lie_logComponent_eq_zero {g g' : d.completedBCHGroup ℒ}
    (h : ∀ n m, ⁅(d.logComponent ℒ g n : L), (d.logComponent ℒ g' m : L)⁆ = 0) :
    Commute g g' := by
  apply CompletedGroup.ext
  intro k
  rw [map_mul, map_mul,
    ← BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
    ← BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g'),
    log_projection_eq_mkQ_sum, log_projection_eq_mkQ_sum]
  refine (BCHGroup.commute_exp_of_lie_eq_zero _ _ ?_).eq
  rw [← LieHom.map_lie, sum_lie]
  simp only [lie_sum, h, Finset.sum_const_zero, map_zero]

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

section DegreeFiltration

open scoped commutatorElement

variable {ℒ}

/-- A completed label lies in the degree filtration above order `a` exactly when its
logarithmic coefficients vanish in every degree at most `a`. -/
theorem mem_degreeFiltration_succ_iff {g : d.completedBCHGroup ℒ} {a : ℕ} :
    g ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) ↔
      ∀ n, d.degree n ≤ a → d.logComponent ℒ g n = 0 := by
  rw [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker]
  constructor
  · intro hg n hn
    have h0 : (d.degreeIdeal ℒ a).mkQ 0 =
        BCHGroup.log (L := d.truncatedLie ℒ a) (CompletedGroup.projection a g) :=
      (map_zero _).trans ((congrArg (BCHGroup.log (L := d.truncatedLie ℒ a)) hg).trans
        (BCHGroup.log_one (L := d.truncatedLie ℒ a))).symm
    rw [d.logComponent_eq_decompose ℒ g hn h0, DirectSum.decompose_zero]
    rfl
  · intro hg
    rw [← BCHGroup.exp_log (L := d.truncatedLie ℒ a) (CompletedGroup.projection a g),
      log_projection_eq_mkQ_sum]
    rw [Finset.sum_eq_zero fun n hn => by
      rw [hg n (d.mem_cutoff.mp ((d.finite_cutoff a).mem_toFinset.mp hn)).2,
        ZeroMemClass.coe_zero]]
    rw [map_zero]
    rfl

/-- Logarithmic coefficients add on the degree filtration above order `a`, in every degree
at most `2 a + 1`: there the two labels commute, and their logarithms add. -/
theorem logComponent_mul_of_mem_degreeFiltration {g h : d.completedBCHGroup ℒ} {a : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    (hh : h ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    {n : N} (hn : d.degree n ≤ a + a + 1) :
    d.logComponent ℒ (g * h) n = d.logComponent ℒ g n + d.logComponent ℒ h n := by
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ (a + a + 1)).surjective_mkQ
    (BCHGroup.log (L := d.truncatedLie ℒ (a + a + 1))
      (CompletedGroup.projection (a + a + 1) g))
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ (a + a + 1)).surjective_mkQ
    (BCHGroup.log (L := d.truncatedLie ℒ (a + a + 1))
      (CompletedGroup.projection (a + a + 1) h))
  have hxa := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ (by omega) g hx).mpr hg
  have hya := (d.mem_degreeIdeal_iff_of_mkQ_eq_log_projection ℒ (by omega) h hy).mpr hh
  have hlie : ⁅(d.degreeIdeal ℒ (a + a + 1)).mkQ x, (d.degreeIdeal ℒ (a + a + 1)).mkQ y⁆ = 0 := by
    rw [← LieHom.map_lie, LieIdeal.mkQ_eq_zero]
    exact d.lie_degreeIdeal_le ℒ a a (LieSubmodule.lie_mem_lie hxa hya)
  have hexp : BCHGroup.exp ((d.degreeIdeal ℒ (a + a + 1)).mkQ (x + y)) =
      CompletedGroup.projection (a + a + 1) g * CompletedGroup.projection (a + a + 1) h := by
    rw [map_add, BCHGroup.exp_add_of_lie_eq_zero _ _ hlie, hx, hy,
      BCHGroup.exp_log (L := d.truncatedLie ℒ (a + a + 1))
        (CompletedGroup.projection (a + a + 1) g),
      BCHGroup.exp_log (L := d.truncatedLie ℒ (a + a + 1))
        (CompletedGroup.projection (a + a + 1) h)]
    -- The products in the group tower and in the BCH group are the same operation.
    rfl
  have hxy : (d.degreeIdeal ℒ (a + a + 1)).mkQ (x + y) =
      BCHGroup.log (L := d.truncatedLie ℒ (a + a + 1))
        (CompletedGroup.projection (a + a + 1) (g * h)) := by
    rw [map_mul]
    exact (BCHGroup.log_exp _).symm.trans (congrArg BCHGroup.log hexp)
  rw [d.logComponent_eq_decompose ℒ _ hn hxy, d.logComponent_eq_decompose ℒ g hn hx,
    d.logComponent_eq_decompose ℒ h hn hy, DirectSum.decompose_add, DirectSum.add_apply]

/-- Conjugation fixes the logarithmic coefficients of a label in the degree filtration above
order `a`, in every degree at most `a + 1`. -/
theorem logComponent_conj_of_mem_degreeFiltration (u : d.completedBCHGroup ℒ)
    {g : d.completedBCHGroup ℒ} {a : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    {n : N} (hn : d.degree n ≤ a + 1) :
    d.logComponent ℒ (u * g * u⁻¹) n = d.logComponent ℒ g n := by
  have hc : ⁅u, g⁆ ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1 + 1) :=
    d.commutator_top_degreeFiltration_le ℒ (a + 1)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hg)
  have hc' : ⁅u, g⁆ ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) :=
    CompletedGroup.degreeFiltration_antitone _ (by omega) hc
  have he : u * g * u⁻¹ = ⁅u, g⁆ * g := by
    rw [commutatorElement_def]
    group
  rw [he, d.logComponent_mul_of_mem_degreeFiltration hc' hg (by omega),
    d.mem_degreeFiltration_succ_iff.mp hc n hn, zero_add]

/-- Removing the factors that lie in the degree filtration above order `a` from a finite
product leaves the logarithmic coefficients in every degree at most `a + 1` equal to the sum
of those of the removed factors: modulo the next filtration step, the removed factors are
central and their coefficients add. The remaining factors are arbitrary. -/
theorem logComponent_inv_prod_filter_mul_prod {ι : Type*} (l : List ι)
    (x : ι → d.completedBCHGroup ℒ) (p : ι → Prop) [DecidablePred p] {a : ℕ}
    (hx : ∀ i ∈ l, ¬p i → x i ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1))
    {n : N} (hn : d.degree n ≤ a + 1) :
    d.logComponent ℒ (((l.filter p).map x).prod⁻¹ * (l.map x).prod) n =
      ((l.filter fun i => ¬p i).map fun i => d.logComponent ℒ (x i) n).sum := by
  suffices h : ((l.filter p).map x).prod⁻¹ * (l.map x).prod ∈
      CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) ∧
      ∀ m, d.degree m ≤ a + 1 →
        d.logComponent ℒ (((l.filter p).map x).prod⁻¹ * (l.map x).prod) m =
          ((l.filter fun i => ¬p i).map fun i => d.logComponent ℒ (x i) m).sum from h.2 n hn
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨ihm, ihc⟩ := ih fun j hj => hx j (List.mem_cons_of_mem i hj)
    by_cases hi : p i
    · have he : ((i :: l).filter p).map x = x i :: (l.filter p).map x := by
        simp [hi]
      have he' : (i :: l).filter (fun i => ¬p i) = l.filter fun i => ¬p i := by
        simp [hi]
      simp only [he, he', List.prod_cons, List.map_cons, mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
      exact ⟨ihm, ihc⟩
    · set u := ((l.filter p).map x).prod
      have hxi := hx i List.mem_cons_self hi
      have he : ((i :: l).filter p).map x = (l.filter p).map x := by
        simp [hi]
      have he' : (i :: l).filter (fun i => ¬p i) = i :: l.filter fun i => ¬p i := by
        simp [hi]
      have hsplit : u⁻¹ * (x i * (l.map x).prod) =
          (u⁻¹ * x i * u⁻¹⁻¹) * (u⁻¹ * (l.map x).prod) := by group
      have hconj :
          u⁻¹ * x i * u⁻¹⁻¹ ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (a + 1) :=
        (CompletedGroup.degreeFiltration_normal _ (a + 1)).conj_mem _ hxi _
      simp only [he, he', List.map_cons, List.prod_cons, List.sum_cons]
      refine ⟨hsplit ▸ Subgroup.mul_mem _ hconj ihm, fun m hm => ?_⟩
      rw [hsplit, d.logComponent_mul_of_mem_degreeFiltration hconj ihm (by omega),
        d.logComponent_conj_of_mem_degreeFiltration u⁻¹ hxi hm, ihc m hm]

end DegreeFiltration

end Mei.PositiveDegrees
