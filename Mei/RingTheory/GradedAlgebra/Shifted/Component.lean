/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Component

/-!
# Homogeneous components of completed shifted products

The component of relative degree `n` in a product of completed shifted coefficients
is the finite convolution over pairs of allowed degrees adding to `n`. The sum
depends only on the positive monoid, independently of a cutoff or representatives.
In particular, the leading component is the product of the leading components.
These formulas allow coefficientwise multiplication of formal theta series, with
arbitrary ambient shifts and without commutativity of the coefficient algebra.

We use the finite addition fibers of `PositiveDegrees` and the quotient-wise
product `shiftedCompletionMul`. The finite-cutoff computation follows the
convolution argument of `Mei.Algebra.Lie.Graded.Product`, with multiplication in
place of the Lie bracket, and uses Mathlib's homogeneous decomposition formulas.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

open _root_.DirectSum

variable {R A Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (𝒜 : Γ → Submodule R A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]
  (p q : Γ)

private theorem decompose_mul_cutoff (x : ∀ n, 𝒜 (p + n)) (y : ∀ n, 𝒜 (q + n)) (n : Γ) :
    (decompose 𝒜
      ((∑ a ∈ (d.finite_cutoff (d.degree n).toNat).toFinset, (x a : A)) *
        ∑ b ∈ (d.finite_cutoff (d.degree n).toNat).toFinset, (y b : A))
      (p + q + n) : A) =
      ∑ ab ∈ (d.finite_decompositions n).toFinset, (x ab.1 : A) * y ab.2 := by
  classical
  have hhom (a b : Γ) : (x a : A) * y b ∈ 𝒜 (p + q + (a + b)) := by
    convert SetLike.mul_mem_graded (x a).property (y b).property using 1
    abel_nf
  have hproj (a b : Γ) :
      (decompose 𝒜 ((x a : A) * y b) (p + q + n) : A) =
        if a + b = n then (x a : A) * y b else 0 := by
    split_ifs with h
    · exact decompose_of_mem_same 𝒜 (h ▸ hhom a b)
    · exact decompose_of_mem_ne 𝒜 (hhom a b) (by simpa using h)
  simp only [Finset.sum_mul_sum, decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [hproj]
  rw [← Finset.sum_product (f := fun ab : Γ × Γ =>
    if ab.1 + ab.2 = n then (x ab.1 : A) * y ab.2 else 0), ← Finset.sum_filter,
    d.filter_cutoff_product_eq_decompositions n _ (Int.self_le_toNat _)]

/-- Each component of a completed shifted product is a finite convolution over
the actual allowed relative degrees. This includes degrees outside the positive
monoid, where the sum is empty. The order of the factors is retained. -/
theorem shiftedHomogeneousComponent_shiftedCompletionMul
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) (n : Γ) :
    (d.shiftedHomogeneousComponent 𝒜 (p + q) (p + q + n)
        (d.shiftedCompletionMul 𝒜 p q x y) : A) =
      ∑ ab ∈ (d.finite_decompositions n).toFinset,
        (d.shiftedHomogeneousComponent 𝒜 p (p + ab.1) x : A) *
          d.shiftedHomogeneousComponent 𝒜 q (q + ab.2) y := by
  classical
  let k := (d.degree n).toNat
  let u : shiftedSubmodule 𝒜 d.monoid p :=
    ∑ a ∈ (d.finite_cutoff k).toFinset.attach,
      shiftedInclusion 𝒜 d.monoid p ⟨a.val, (d.mem_cutoff.mp
        ((d.finite_cutoff k).mem_toFinset.mp a.property)).1⟩
        (d.shiftedHomogeneousComponent 𝒜 p (p + a.val) x)
  let v : shiftedSubmodule 𝒜 d.monoid q :=
    ∑ a ∈ (d.finite_cutoff k).toFinset.attach,
      shiftedInclusion 𝒜 d.monoid q ⟨a.val, (d.mem_cutoff.mp
        ((d.finite_cutoff k).mem_toFinset.mp a.property)).1⟩
        (d.shiftedHomogeneousComponent 𝒜 q (q + a.val) y)
  rw [d.shiftedHomogeneousComponent_eq 𝒜 (p + q) (p + q + n) k
    (by simpa only [add_sub_cancel_left, k] using Int.self_le_toNat (d.degree n))]
  rw [d.projection_shiftedCompletionMul 𝒜 p q k x y u v
    (d.projection_eq_sum_shiftedHomogeneousComponent 𝒜 p k x).symm
    (d.projection_eq_sum_shiftedHomogeneousComponent 𝒜 q k y).symm,
    shiftedQuotientComponent_mk, coe_shiftedMul]
  simp only [u, v, Submodule.coe_sum, coe_shiftedInclusion]
  rw [Finset.sum_attach _ (fun a => (d.shiftedHomogeneousComponent 𝒜 p (p + a) x : A)),
    Finset.sum_attach _ (fun a => (d.shiftedHomogeneousComponent 𝒜 q (q + a) y : A))]
  exact d.decompose_mul_cutoff 𝒜 p q
      (fun a => d.shiftedHomogeneousComponent 𝒜 p (p + a) x)
      (fun a => d.shiftedHomogeneousComponent 𝒜 q (q + a) y) n

/-- The leading homogeneous component of a completed shifted product is the
product of the leading components, even when the ambient shifts are negative. -/
@[simp]
theorem shiftedHomogeneousComponent_shiftedCompletionMul_zero
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    (d.shiftedHomogeneousComponent 𝒜 (p + q) (p + q)
        (d.shiftedCompletionMul 𝒜 p q x y) : A) =
      (d.shiftedHomogeneousComponent 𝒜 p p x : A) *
        d.shiftedHomogeneousComponent 𝒜 q q y := by
  have hf : (d.finite_decompositions 0).toFinset = {(0, 0)} := by
    ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨ha, hb, hab⟩
      have ha0 : a = 0 := (d.degree_eq_zero_iff ha).mp
        (le_antisymm (by simpa using d.degree_le_of_add_eq hb hab) (d.degree_nonneg ha))
      exact ⟨ha0, by simpa [ha0] using hab⟩
    · rintro ⟨rfl, rfl⟩
      simp
  have h := d.shiftedHomogeneousComponent_shiftedCompletionMul 𝒜 p q x y 0
  rw [add_zero, hf, Finset.sum_singleton, add_zero, add_zero] at h
  exact h

end Mei.PositiveDegrees
