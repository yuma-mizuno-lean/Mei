/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Completion
public import Mei.Algebra.PositiveDegrees.Completion
public import Mathlib.Algebra.Lie.TransferInstance

/-!
# The Lie algebra of homogeneous coefficient families

For a positively graded Lie algebra, arbitrary families of homogeneous coefficients
form a Lie algebra. Its bracket is convolution: the coefficient at `n` is the finite
sum of brackets of coefficients at allowed degrees `a, b` with `a + b = n`.
The coefficient comparison identifies this Lie algebra with the degree completion.

The construction uses `PositiveDegrees.completionEquivPi` and Mathlib's
`AddEquiv.lieRing` and `LinearEquiv.lieAlgebra` to transport the Lie laws. The
convolution formula is proved from finite quotient representatives, so it describes
the bracket without unfolding the transported structure. No basis or finite rank
assumption on the homogeneous pieces is needed.
-/

public section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" => LieIdeal.completionFiltration (d.degreeIdeal ℒ)
  (d.degreeIdeal_antitone ℒ)
local notation "E" => d.completionEquivPi ℒ F
  (fun k => d.degreeIdeal_toSubmodule ℒ k)
  (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn))

/-- The convolution Lie ring on homogeneous coefficient families.
Install this structure locally when using the product as a Lie algebra. -/
@[instance_reducible]
noncomputable def homogeneousProductLieRing : LieRing (∀ n, ℒ n) :=
  (E).symm.toAddEquiv.lieRing

/-- The convolution bracket is linear over the original coefficient ring. -/
@[instance_reducible]
noncomputable def homogeneousProductLieAlgebra :
    letI := d.homogeneousProductLieRing ℒ
    LieAlgebra R (∀ n, ℒ n) :=
  letI := d.homogeneousProductLieRing ℒ
  (E).symm.lieAlgebra

/-- Homogeneous coefficients identify the degree completion with the convolution Lie algebra. -/
noncomputable def completedLieEquivPi :
    letI := d.homogeneousProductLieRing ℒ
    letI := d.homogeneousProductLieAlgebra ℒ
    d.completedLie ℒ ≃ₗ⁅R⁆ ∀ n, ℒ n :=
  letI := d.homogeneousProductLieRing ℒ
  letI := d.homogeneousProductLieAlgebra ℒ
  ((E).symm.lieEquiv R).symm

/-- The Lie comparison reads the existing completed homogeneous components. -/
@[simp]
theorem completedLieEquivPi_apply (x : d.completedLie ℒ) (n : N) :
    d.completedLieEquivPi ℒ x n =
      d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n x := by
  simpa only [completedLieEquivPi, LinearEquiv.lieEquiv_symm_apply,
    LinearEquiv.symm_symm] using
    d.completionEquivPi_apply ℒ F _ _ x n

/-- Reconstructing a coefficient family gives exactly the prescribed coefficients. -/
@[simp]
theorem completionComponent_completedLieEquivPi_symm (x : ∀ n, ℒ n) (n : N) :
    letI := d.homogeneousProductLieRing ℒ
    letI := d.homogeneousProductLieAlgebra ℒ
    d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n
      ((d.completedLieEquivPi ℒ).symm x) = x n := by
  let _ := d.homogeneousProductLieRing ℒ
  let _ := d.homogeneousProductLieAlgebra ℒ
  rw [← completedLieEquivPi_apply, LieEquiv.apply_symm_apply]

/-- The inverse comparison at order `k` is represented by the finite cutoff sum. -/
theorem projection_completedLieEquivPi_symm (x : ∀ n, ℒ n) (k : ℕ) :
    letI := d.homogeneousProductLieRing ℒ
    letI := d.homogeneousProductLieAlgebra ℒ
    (F).projection k ((d.completedLieEquivPi ℒ).symm x) =
      Submodule.Quotient.mk (∑ n ∈ (d.finite_cutoff k).toFinset, (x n : L)) := by
  simpa only [completedLieEquivPi, LieEquiv.symm_symm, LinearEquiv.lieEquiv_apply] using
    d.projection_completionEquivPi_symm ℒ F _ _ x k

omit [IsPositiveGrading d ℒ] in
private theorem component_bracket_finiteSums (x y : ∀ n, ℒ n) (n : N) (k : ℕ)
    (hn : d.degree n ≤ k) :
    (decompose ℒ ⁅∑ a ∈ (d.finite_cutoff k).toFinset, (x a : L),
      ∑ b ∈ (d.finite_cutoff k).toFinset, (y b : L)⁆ n : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset, ⁅(x p.1 : L), (y p.2 : L)⁆ := by
  classical
  let S := (d.finite_cutoff k).toFinset
  let D := (d.finite_decompositions n).toFinset
  have hDS : D ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨ha, hb, hab⟩ := (d.finite_decompositions n).mem_toFinset.mp hp
    exact Finset.mem_product.mpr
      ⟨(d.finite_cutoff k).mem_toFinset.mpr
        ((d.mem_cutoff).mpr ⟨ha, (d.degree_le_of_add_eq hb hab).trans hn⟩),
       (d.finite_cutoff k).mem_toFinset.mpr
        ((d.mem_cutoff).mpr
          ⟨hb, (d.degree_le_of_add_eq ha (by simpa [add_comm] using hab)).trans hn⟩)⟩
  have hhom (a b : N) : ⁅(x a : L), (y b : L)⁆ ∈ ℒ (a + b) :=
    SetLike.GradedBracket.bracket_mem (x a).property (y b).property
  calc
    _ = ∑ p ∈ S ×ˢ S, (decompose ℒ ⁅(x p.1 : L), (y p.2 : L)⁆ n : L) := by
      simp only [sum_lie_sum, decompose_sum, DirectSum.sum_apply, Submodule.coe_sum,
        Finset.sum_product, S]
    _ = ∑ p ∈ D, (decompose ℒ ⁅(x p.1 : L), (y p.2 : L)⁆ n : L) := by
      symm
      apply Finset.sum_subset hDS
      intro p hp hnot
      have hab : p.1 + p.2 ≠ n := by
        intro he
        have hp' := Finset.mem_product.mp hp
        exact hnot ((d.finite_decompositions n).mem_toFinset.mpr
          ⟨((d.mem_cutoff).mp ((d.finite_cutoff k).mem_toFinset.mp hp'.1)).1,
           ((d.mem_cutoff).mp ((d.finite_cutoff k).mem_toFinset.mp hp'.2)).1, he⟩)
      exact decompose_of_mem_ne ℒ (hhom p.1 p.2) hab
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hab := ((d.finite_decompositions n).mem_toFinset.mp hp).2.2
      exact decompose_of_mem_same ℒ (hab ▸ hhom p.1 p.2)

/-- Each coefficient of the product bracket is the finite convolution over actual
allowed degree decompositions. This also applies to degrees outside the positive monoid. -/
theorem homogeneousProduct_bracket_apply (x y : ∀ n, ℒ n) (n : N) :
    letI := d.homogeneousProductLieRing ℒ
    (⁅x, y⁆ n : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset, ⁅(x p.1 : L), (y p.2 : L)⁆ := by
  let _ := d.homogeneousProductLieRing ℒ
  let _ := d.homogeneousProductLieAlgebra ℒ
  let k := (d.degree n).toNat
  have hn : d.degree n ≤ k := Int.self_le_toNat _
  have he : ⁅x, y⁆ = d.completedLieEquivPi ℒ
      ⁅(d.completedLieEquivPi ℒ).symm x, (d.completedLieEquivPi ℒ).symm y⁆ := by
    rw [LieEquiv.map_lie, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
  rw [he, completedLieEquivPi_apply,
    d.completionComponent_eq_quotientComponent ℒ F _ n k hn,
    LieIdeal.projection_bracket, projection_completedLieEquivPi_symm,
    projection_completedLieEquivPi_symm]
  -- The quotient Lie bracket is represented by the bracket of representatives.
  rw [← LieSubmodule.Quotient.mk_bracket, quotientComponent_mk]
  exact d.component_bracket_finiteSums ℒ x y n k hn

/-- The coefficient formula for the bracket of two arbitrary completed Lie elements. -/
theorem completedLieEquivPi_bracket_apply (x y : d.completedLie ℒ) (n : N) :
    (d.completedLieEquivPi ℒ ⁅x, y⁆ n : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset,
        ⁅(d.completedLieEquivPi ℒ x p.1 : L), (d.completedLieEquivPi ℒ y p.2 : L)⁆ := by
  let _ := d.homogeneousProductLieRing ℒ
  let _ := d.homogeneousProductLieAlgebra ℒ
  rw [LieEquiv.map_lie]
  exact d.homogeneousProduct_bracket_apply ℒ _ _ n

end Mei.PositiveDegrees
