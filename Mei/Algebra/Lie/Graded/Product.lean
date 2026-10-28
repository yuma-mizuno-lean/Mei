/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Completion
public import Mei.Algebra.PositiveDegrees.Completion

/-!
# The convolution Lie algebra of homogeneous products

For a positively graded Lie algebra, arbitrary families of homogeneous elements
carry the convolution bracket: its degree-`n` coefficient is the sum of brackets
over all allowed pairs of degrees adding to `n`. Positive degree data make this
sum finite. The coefficient comparison identifies this Lie algebra with the
compatible-family degree completion, without a basis or dimension hypothesis.

Use `letI := d.lieRingPi ℒ` and `letI := d.lieAlgebraPi ℒ` to equip the product
with this structure. These are explicit choices because the positive degree data
are not determined by the type of the product.

The linear comparison and its finite-cutoff reconstruction are
`Mei.PositiveDegrees.completionEquivPi`. The verification of the Lie identities
uses the quotient-wise bracket on `LieIdeal.completion`, following Mathlib's
transport construction `DirectSum.decomposeLieEquiv` for direct sums.
-/

public section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
section Bracket

variable [SetLike.GradedBracket ℒ ℒ]

/-- The finite convolution of two homogeneous families, with sums indexed by
allowed degree decompositions. This operation requires only a homogeneous bracket. -/
noncomputable def piLieBracket (x y : ∀ n, ℒ n) (n : N) : ℒ n :=
  ⟨∑ p ∈ (d.finite_decompositions n).toFinset, ⁅(x p.1 : L), (y p.2 : L)⁆,
    Submodule.sum_mem _ (fun p hp => by
      have hp' := (d.finite_decompositions n).mem_toFinset.mp hp
      rw [← hp'.2.2]
      exact SetLike.GradedBracket.bracket_mem (x p.1).property (y p.2).property)⟩

/-- Each coefficient of the homogeneous convolution is the finite sum of brackets
over all allowed pairs adding to that degree. -/
@[simp]
theorem piLieBracket_apply (x y : ∀ n, ℒ n) (n : N) :
    (d.piLieBracket ℒ x y n : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset, ⁅(x p.1 : L), (y p.2 : L)⁆ := (rfl)

end Bracket

variable [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "F" =>
  LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

private noncomputable abbrev productEquiv :=
  d.completionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
    (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn))

omit [IsPositiveGrading d ℒ] in
private theorem decompose_lie_cutoff (x y : ∀ n, ℒ n) (n : N) :
    (decompose ℒ
      ⁅∑ a ∈ (d.finite_cutoff (d.degree n).toNat).toFinset, (x a : L),
       ∑ b ∈ (d.finite_cutoff (d.degree n).toNat).toFinset, (y b : L)⁆ n : L) =
      (piLieBracket d ℒ x y n : L) := by
  classical
  have hhom (a b : N) : ⁅(x a : L), (y b : L)⁆ ∈ ℒ (a + b) :=
    SetLike.GradedBracket.bracket_mem (x a).property (y b).property
  have hproj (a b : N) :
      (decompose ℒ ⁅(x a : L), (y b : L)⁆ n : L) =
        if a + b = n then ⁅(x a : L), (y b : L)⁆ else 0 := by
    split_ifs with h
    · exact decompose_of_mem_same ℒ (h ▸ hhom a b)
    · exact decompose_of_mem_ne ℒ (hhom a b) h
  simp only [sum_lie_sum, decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [hproj]
  rw [← Finset.sum_product (f := fun p : N × N =>
    if p.1 + p.2 = n then ⁅(x p.1 : L), (y p.2 : L)⁆ else 0),
    ← Finset.sum_filter,
    d.filter_cutoff_product_eq_decompositions n _ (Int.self_le_toNat _), piLieBracket_apply]

private theorem component_lie_inverse (x y : ∀ n, ℒ n) (n : N) :
    d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n
      ⁅(productEquiv d ℒ).symm x, (productEquiv d ℒ).symm y⁆ =
        piLieBracket d ℒ x y n := by
  classical
  rw [completionComponent_eq_quotientComponent d ℒ _ _ n (d.degree n).toNat
    (Int.self_le_toNat _), LieIdeal.projection_bracket]
  rw [projection_completionEquivPi_symm, projection_completionEquivPi_symm,
    ← LieSubmodule.Quotient.mk_bracket, quotientComponent_mk]
  exact Subtype.ext (decompose_lie_cutoff d ℒ x y n)

private theorem productEquiv_lie (x y : d.completedLie ℒ) :
    productEquiv d ℒ ⁅x, y⁆ =
      piLieBracket d ℒ (productEquiv d ℒ x) (productEquiv d ℒ y) := by
  funext n
  simpa only [LinearEquiv.symm_apply_apply, completionEquivPi_apply] using
    component_lie_inverse d ℒ (productEquiv d ℒ x) (productEquiv d ℒ y) n

/-- The convolution Lie ring on all homogeneous families. Use as a local instance;
the positive degree data cannot be inferred from the product type. -/
-- The inherited operations must compute to retain the usual componentwise addition.
@[expose, instance_reducible]
noncomputable def lieRingPi : LieRing (∀ n, ℒ n) where
  bracket := piLieBracket d ℒ
  add_lie x y z := by
    obtain ⟨x, rfl⟩ := (productEquiv d ℒ).surjective x
    obtain ⟨y, rfl⟩ := (productEquiv d ℒ).surjective y
    obtain ⟨z, rfl⟩ := (productEquiv d ℒ).surjective z
    simp only [← map_add, ← productEquiv_lie, add_lie]
  lie_add x y z := by
    obtain ⟨x, rfl⟩ := (productEquiv d ℒ).surjective x
    obtain ⟨y, rfl⟩ := (productEquiv d ℒ).surjective y
    obtain ⟨z, rfl⟩ := (productEquiv d ℒ).surjective z
    simp only [← map_add, ← productEquiv_lie, lie_add]
  lie_self x := by
    obtain ⟨x, rfl⟩ := (productEquiv d ℒ).surjective x
    rw [← productEquiv_lie, lie_self, map_zero]
  leibniz_lie x y z := by
    obtain ⟨x, rfl⟩ := (productEquiv d ℒ).surjective x
    obtain ⟨y, rfl⟩ := (productEquiv d ℒ).surjective y
    obtain ⟨z, rfl⟩ := (productEquiv d ℒ).surjective z
    simp only [← productEquiv_lie, ← map_add]
    exact congrArg (productEquiv d ℒ) (leibniz_lie x y z)

/-- The convolution bracket is compatible with the componentwise scalar action. -/
-- The inherited module must compute to retain the usual componentwise scalar action.
@[expose, instance_reducible]
noncomputable def lieAlgebraPi :
    letI := d.lieRingPi ℒ
    LieAlgebra R (∀ n, ℒ n) := by
  letI := d.lieRingPi ℒ
  exact
    { lie_smul := fun r x y => by
        obtain ⟨x, rfl⟩ := (productEquiv d ℒ).surjective x
        obtain ⟨y, rfl⟩ := (productEquiv d ℒ).surjective y
        -- The chosen bracket is the convolution field of the explicit Lie ring structure.
        change piLieBracket d ℒ _ _ = r • piLieBracket d ℒ _ _
        simp only [← map_smul, ← productEquiv_lie, lie_smul] }

/-- The Lie ring bracket is the homogeneous convolution operation. -/
@[simp]
theorem lieRingPi_bracket (x y : ∀ n, ℒ n) :
    letI := d.lieRingPi ℒ
    ⁅x, y⁆ = d.piLieBracket ℒ x y := (rfl)

/-- Homogeneous coefficients identify the completed Lie algebra with the convolution
Lie algebra on the product of its homogeneous pieces. -/
noncomputable def completionLieEquivPi :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    d.completedLie ℒ ≃ₗ⁅R⁆ ∀ n, ℒ n := by
  letI := d.lieRingPi ℒ
  letI := d.lieAlgebraPi ℒ
  exact { productEquiv d ℒ with map_lie' := fun {x y} => productEquiv_lie d ℒ x y }

/-- Forgetting the bracket recovers the original module comparison, so its
finite-cutoff reconstruction and filtration characterizations apply unchanged. -/
@[simp]
theorem completionLieEquivPi_toLinearEquiv :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    (d.completionLieEquivPi ℒ).toLinearEquiv =
      d.completionEquivPi ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k)
        (fun n hn => IsPositiveGrading.eq_bot n (Or.inl hn)) := (rfl)

/-- The Lie comparison reads the same coefficients as the module comparison. -/
@[simp]
theorem completionLieEquivPi_apply (x : d.completedLie ℒ) (n : N) :
    d.completionLieEquivPi ℒ x n =
      d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n x :=
  d.completionEquivPi_apply ℒ F _ _ x n

/-- The inverse Lie comparison reconstructs any family of homogeneous coefficients. -/
@[simp]
theorem completionComponent_completionLieEquivPi_symm (x : ∀ n, ℒ n) (n : N) :
    letI := d.lieRingPi ℒ
    letI := d.lieAlgebraPi ℒ
    d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n
      ((d.completionLieEquivPi ℒ).symm x) = x n :=
  d.completionComponent_completionEquivPi_symm ℒ _ _ _ x n

/-- The completed Lie bracket has the finite convolution formula on homogeneous
coefficients, expressed directly on the compatible-family completion. -/
theorem completionComponent_lie (x y : d.completedLie ℒ) (n : N) :
    (d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) n ⁅x, y⁆ : L) =
      ∑ p ∈ (d.finite_decompositions n).toFinset,
        ⁅(d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) p.1 x : L),
         (d.completionComponent ℒ F (fun k => d.degreeIdeal_toSubmodule ℒ k) p.2 y : L)⁆ := by
  simpa only [piLieBracket, completionEquivPi_apply] using
    congrArg (fun z : ∀ n, ℒ n => (z n : L)) (productEquiv_lie d ℒ x y)

end Mei.PositiveDegrees
