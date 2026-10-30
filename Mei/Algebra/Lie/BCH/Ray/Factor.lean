/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Basic

/-!
# Supported-ray factors of completed BCH labels

A completed BCH label has a homogeneous logarithmic coefficient in every degree. Keeping
the coefficients in the actual degrees of one supported ray, and discarding all others,
gives its *ray factor* on that ray. Ray factors are completed ray labels, they leave a
label on a single ray unchanged, and only finitely many of them are nontrivial at each
order. When the coefficients of a label commute pairwise, for instance when they lie in an
abelian Lie subalgebra, the label is at every order the unordered product of its ray
factors over any finite set of rays containing those that meet the cutoff.

This is the splitting of a function wall into supported-ray walls: the label
`exp(log(f) ∂_ν)` of a wall function `f` with terms in several directions tangent to `ν`
has commuting coefficients, and its ray factors are the labels `exp((log f)_w ∂_ν)` of the
ray presentation (Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1.1, arXiv:1411.1394v2; Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §9.2, arXiv:2503.03719v1).

The ray factor reassembles the selected coefficients through the product description
`Mei.PositiveDegrees.completionEquivPi` of the degree completion and the exponential
coordinate `Mei.PositiveDegrees.completedBCHExp`. The product formula combines
`Mei.PositiveDegrees.log_projection_eq_mkQ_sum` with `Mei.BCHGroup.exp_sum_of_lie_eq_zero`,
using that every nonzero allowed degree lies on exactly one supported ray.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

open Classical in
/-- The ray factor of a completed label on a supported ray: the completed label whose
logarithmic coefficients are those of `g` in the actual degrees of `w` and zero elsewhere. -/
def rayFactor (g : d.completedBCHGroup ℒ) (w : SupportedRay d) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ ((d.completionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
    (fun _ hn => IsPositiveGrading.eq_bot _ (Or.inl hn))).symm
      fun n => if n ∈ w.rayDegrees then d.logComponent ℒ g n else 0)

/-- On an actual degree of the ray, the ray factor keeps the logarithmic coefficient. -/
@[simp]
theorem logComponent_rayFactor_of_mem (g : d.completedBCHGroup ℒ) {w : SupportedRay d}
    {n : N} (hn : n ∈ w.rayDegrees) :
    d.logComponent ℒ (d.rayFactor ℒ g w) n = d.logComponent ℒ g n := by
  rw [rayFactor, logComponent_completedBCHExp, completionComponent_completionEquivPi_symm,
    ite_eq_left hn]

/-- Off the actual degrees of the ray, the ray factor has no logarithmic coefficient. -/
@[simp]
theorem logComponent_rayFactor_of_notMem (g : d.completedBCHGroup ℒ) {w : SupportedRay d}
    {n : N} (hn : n ∉ w.rayDegrees) : d.logComponent ℒ (d.rayFactor ℒ g w) n = 0 := by
  rw [rayFactor, logComponent_completedBCHExp, completionComponent_completionEquivPi_symm,
    ite_eq_right hn]

/-- The ray factors are the unique completed labels with these coefficients. -/
theorem eq_rayFactor_iff {g h : d.completedBCHGroup ℒ} {w : SupportedRay d} :
    h = d.rayFactor ℒ g w ↔
      (∀ n ∈ w.rayDegrees, d.logComponent ℒ h n = d.logComponent ℒ g n) ∧
        ∀ n, n ∉ w.rayDegrees → d.logComponent ℒ h n = 0 := by
  constructor
  · rintro rfl
    exact ⟨fun n hn => d.logComponent_rayFactor_of_mem ℒ g hn,
      fun n hn => d.logComponent_rayFactor_of_notMem ℒ g hn⟩
  · rintro ⟨hmem, hnot⟩
    apply d.ext_logComponent ℒ
    intro n
    by_cases hn : n ∈ w.rayDegrees
    · rw [hmem n hn, d.logComponent_rayFactor_of_mem ℒ g hn]
    · rw [hnot n hn, d.logComponent_rayFactor_of_notMem ℒ g hn]

/-- Ray factors are completed ray labels. -/
@[simp high]
theorem rayFactor_mem_completedRaySubgroup (g : d.completedBCHGroup ℒ) (w : SupportedRay d) :
    d.rayFactor ℒ g w ∈ d.completedRaySubgroup ℒ w :=
  (d.mem_completedRaySubgroup_iff_logComponent ℒ w _).mpr fun _ hn =>
    d.logComponent_rayFactor_of_notMem ℒ g hn

/-- A label on one supported ray is its own ray factor there. -/
@[simp]
theorem rayFactor_eq_self {g : d.completedBCHGroup ℒ} {w : SupportedRay d}
    (hg : g ∈ d.completedRaySubgroup ℒ w) : d.rayFactor ℒ g w = g :=
  (eq_rayFactor_iff d ℒ).mpr ⟨fun _ _ => rfl,
    (d.mem_completedRaySubgroup_iff_logComponent ℒ w g).mp hg⟩ |>.symm

/-- A label on one supported ray has trivial ray factors on every other ray. -/
theorem rayFactor_eq_one [HasUniqueDiv N] {g : d.completedBCHGroup ℒ} {v w : SupportedRay d}
    (hg : g ∈ d.completedRaySubgroup ℒ v) (hvw : v ≠ w) : d.rayFactor ℒ g w = 1 := by
  apply d.ext_logComponent ℒ
  intro n
  rw [logComponent_one]
  by_cases hn : n ∈ w.rayDegrees
  · rw [d.logComponent_rayFactor_of_mem ℒ g hn]
    exact d.logComponent_eq_zero_of_notMem_rayDegrees ℒ hg
      ((SupportedRay.disjoint_rayDegrees hvw).notMem_of_mem_right hn)
  · exact d.logComponent_rayFactor_of_notMem ℒ g hn

/-- The identity label has trivial ray factors. -/
@[simp high]
theorem rayFactor_one (w : SupportedRay d) : d.rayFactor ℒ 1 w = 1 := by
  apply d.ext_logComponent ℒ
  intro n
  by_cases hn : n ∈ w.rayDegrees
  · rw [d.logComponent_rayFactor_of_mem ℒ 1 hn]
  · rw [d.logComponent_rayFactor_of_notMem ℒ 1 hn, logComponent_one]

/-- Ray factors respect inversion of completed labels. -/
@[simp]
theorem rayFactor_inv (g : d.completedBCHGroup ℒ) (w : SupportedRay d) :
    d.rayFactor ℒ g⁻¹ w = (d.rayFactor ℒ g w)⁻¹ := by
  apply d.ext_logComponent ℒ
  intro n
  by_cases hn : n ∈ w.rayDegrees
  · simp only [logComponent_rayFactor_of_mem d ℒ _ hn, logComponent_inv]
  · simp only [logComponent_rayFactor_of_notMem d ℒ _ hn, logComponent_inv, neg_zero]

/-- Only finitely many ray factors of a label are nontrivial at each order. -/
theorem hasFiniteSupport_rayFactor [HasUniqueDiv N] (g : d.completedBCHGroup ℒ) :
    CompletedGroup.HasFiniteSupport (d.rayFactor ℒ g) :=
  d.hasFiniteSupport_completedRaySubgroup ℒ fun w =>
    ⟨d.rayFactor ℒ g w, d.rayFactor_mem_completedRaySubgroup ℒ g w⟩

open Classical in
/-- At order `k`, the logarithm of a ray factor is the class of the sum of the
coefficients of the label in the actual ray degrees retained at that order. -/
theorem log_projection_rayFactor (g : d.completedBCHGroup ℒ) (w : SupportedRay d) (k : ℕ) :
    BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k (d.rayFactor ℒ g w)) =
      (d.degreeIdeal ℒ k).mkQ (∑ n ∈ (d.finite_cutoff k).toFinset,
        if n ∈ w.rayDegrees then (d.logComponent ℒ g n : L) else 0) := by
  rw [log_projection_eq_mkQ_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hn
  · rw [d.logComponent_rayFactor_of_mem ℒ g hn]
  · rw [d.logComponent_rayFactor_of_notMem ℒ g hn, ZeroMemClass.coe_zero]

variable {ℒ}

/-- The ray factors of a label with pairwise commuting coefficients commute. -/
theorem commute_rayFactor {g : d.completedBCHGroup ℒ}
    (hg : ∀ n m, ⁅(d.logComponent ℒ g n : L), (d.logComponent ℒ g m : L)⁆ = 0)
    (v w : SupportedRay d) : Commute (d.rayFactor ℒ g v) (d.rayFactor ℒ g w) := by
  apply d.commute_of_lie_logComponent_eq_zero
  intro n m
  by_cases hn : n ∈ v.rayDegrees
  · by_cases hm : m ∈ w.rayDegrees
    · rw [d.logComponent_rayFactor_of_mem ℒ g hn, d.logComponent_rayFactor_of_mem ℒ g hm]
      exact hg n m
    · rw [d.logComponent_rayFactor_of_notMem ℒ g hm, ZeroMemClass.coe_zero, lie_zero]
  · rw [d.logComponent_rayFactor_of_notMem ℒ g hn, ZeroMemClass.coe_zero, zero_lie]

/-- A completed label with pairwise commuting logarithmic coefficients is, at every order,
the unordered product of its ray factors over any finite set of supported rays containing
the rays that meet the cutoff. -/
theorem projection_eq_noncommProd_rayFactor [Module.Free ℤ N] {g : d.completedBCHGroup ℒ}
    (hg : ∀ n m, ⁅(d.logComponent ℒ g n : L), (d.logComponent ℒ g m : L)⁆ = 0)
    (k : ℕ) (s : Finset (SupportedRay d)) (hs : d.raysAtOrder k ⊆ s) :
    CompletedGroup.projection k g =
      s.noncommProd (fun w => CompletedGroup.projection k (d.rayFactor ℒ g w))
        (fun v _ w _ _ => (d.commute_rayFactor hg v w).map _) := by
  classical
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  let c := (d.finite_cutoff k).toFinset
  let x (w : SupportedRay d) : L :=
    ∑ n ∈ c, if n ∈ w.rayDegrees then (d.logComponent ℒ g n : L) else 0
  have hx : (s : Set (SupportedRay d)).Pairwise fun v w =>
      ⁅(d.degreeIdeal ℒ k).mkQ (x v), (d.degreeIdeal ℒ k).mkQ (x w)⁆ = 0 := by
    intro v _ w _ _
    rw [← LieHom.map_lie]
    simp only [x, sum_lie, lie_sum]
    refine (congrArg _ (Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun m _ => ?_)).trans
      (map_zero _)
    split_ifs <;> simp [hg]
  -- Each retained nonzero degree lies on exactly one ray of `s`.
  have hsum : ∑ w ∈ s, x w = ∑ n ∈ c, (d.logComponent ℒ g n : L) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hP, hk⟩ := d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp hn)
    by_cases h0 : n = 0
    · subst h0
      have hb : ℒ 0 = ⊥ := IsPositiveGrading.eq_bot (d := d) 0 (Or.inr rfl)
      have hz : (d.logComponent ℒ g 0 : L) = 0 := by
        simpa only [hb, Submodule.mem_bot] using (d.logComponent ℒ g 0).property
      simp [hz]
    obtain ⟨w, hw⟩ := d.exists_supportedRay hP h0
    rw [Finset.sum_eq_single_of_mem w (Finset.mem_coe.mp (hs (d.mem_raysAtOrder.mpr ⟨n, hw, hk⟩))),
      ite_eq_left hw]
    intro v _ hvw
    exact ite_eq_right fun hv => hvw (SupportedRay.eq_of_mem_rayDegrees hv hw)
  rw [← BCHGroup.exp_log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g),
    log_projection_eq_mkQ_sum, ← hsum, map_sum, BCHGroup.exp_sum_of_lie_eq_zero s _ hx]
  refine Finset.noncommProd_congr rfl (fun w _ => ?_) _
  rw [← d.log_projection_rayFactor ℒ g w k]
  exact BCHGroup.exp_log (L := d.truncatedLie ℒ k) _

end Mei.PositiveDegrees
