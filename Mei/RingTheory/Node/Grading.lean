/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.SignedMonomial
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The normal-weight grading of a nodal algebra

The algebra `R[X,Y]/(XY-a)` is graded by `deg X = -1` and `deg Y = 1`,
with `R` in weight zero. Each weight is the span of its signed monomial.
The left Laurent map is injective on every nonpositive weight, and the right
Laurent map on every nonnegative weight, even when `a` is a zero divisor.
These statements make incoming lifts unique within their prescribed weight.

We use `signedMonomialBasis` and its multiplication formula, together with
Mathlib's internal-direct-sum construction of graded algebras. The normal-form
interpretation is that of Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra LaurentPolynomial Module

variable {R : Type*} [CommRing R] (a : R)

/-- Weight `n` consists of multiples of `X^(-n)` for `n ≤ 0`, and of `Y^n`
for `n ≥ 0`. The nodal parameter has weight zero. -/
def normalWeight (n : ℤ) : Submodule R (NodeAlgebra R a) :=
  R ∙ signedMonomial a n

/-- A homogeneous element is a scalar multiple of the corresponding signed monomial. -/
@[simp]
theorem mem_normalWeight_iff (n : ℤ) (z : NodeAlgebra R a) :
    z ∈ normalWeight a n ↔ ∃ c : R, c • signedMonomial a n = z :=
  Submodule.mem_span_singleton

/-- The normal monomial has its prescribed weight. -/
@[simp high]
theorem signedMonomial_mem_normalWeight (n : ℤ) :
    signedMonomial a n ∈ normalWeight a n :=
  Submodule.mem_span_singleton_self _

/-- The normal weights give an internal direct sum, over an arbitrary coefficient ring. -/
theorem isInternal_normalWeight : DirectSum.IsInternal (normalWeight a) := by
  have he : normalWeight a = fun n => R ∙ signedMonomialBasis a n := by
    ext n
    rw [normalWeight, signedMonomialBasis_apply]
  rw [he]
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (signedMonomialBasis a).linearIndependent.iSupIndep_span_singleton
    (by rw [← Submodule.span_range_eq_iSup, (signedMonomialBasis a).span_eq])

instance : SetLike.GradedMonoid (normalWeight a) where
  one_mem := (mem_normalWeight_iff a 0 1).mpr ⟨1, by simp⟩
  mul_mem n m x y hx hy := by
    obtain ⟨c, rfl⟩ := (mem_normalWeight_iff a n x).mp hx
    obtain ⟨d, rfl⟩ := (mem_normalWeight_iff a m y).mp hy
    rw [smul_mul_smul_comm, signedMonomial_mul_signedMonomial, ← map_pow, ← Algebra.smul_def,
      smul_smul]
    exact (normalWeight a (n + m)).smul_mem _ (signedMonomial_mem_normalWeight a _)

/-- The signed normal forms give the multiplicative normal-weight decomposition. -/
instance : GradedAlgebra (normalWeight a) :=
  DirectSum.IsInternal.gradedAlgebra (isInternal_normalWeight a)

/-- The left chamber detects equality within every incoming normal weight. -/
theorem leftLaurentMap_injOn_normalWeight (n : ℤ) (hn : n ≤ 0) :
    Set.InjOn (leftLaurentMap a) (normalWeight a n) := by
  intro x hx y hy hxy
  obtain ⟨c, rfl⟩ := (mem_normalWeight_iff a n x).mp hx
  obtain ⟨d, rfl⟩ := (mem_normalWeight_iff a n y).mp hy
  rw [leftLaurentMap_smul_signedMonomial_of_nonpos a n hn,
    leftLaurentMap_smul_signedMonomial_of_nonpos a n hn] at hxy
  exact congrArg (fun c => c • signedMonomial a n)
    (AddMonoidAlgebra.single_right_injective hxy)

/-- The right chamber detects equality within every incoming normal weight. -/
theorem rightLaurentMap_injOn_normalWeight (n : ℤ) (hn : 0 ≤ n) :
    Set.InjOn (rightLaurentMap a) (normalWeight a n) := by
  intro x hx y hy hxy
  obtain ⟨c, rfl⟩ := (mem_normalWeight_iff a n x).mp hx
  obtain ⟨d, rfl⟩ := (mem_normalWeight_iff a n y).mp hy
  rw [rightLaurentMap_smul_signedMonomial_of_nonneg a n hn,
    rightLaurentMap_smul_signedMonomial_of_nonneg a n hn] at hxy
  exact congrArg (fun c => c • signedMonomial a n)
    (AddMonoidAlgebra.single_right_injective hxy)

end Mei.NodeAlgebra
