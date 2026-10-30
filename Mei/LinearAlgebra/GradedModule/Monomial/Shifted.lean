/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Monomial.Supported
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedModule.Shifted.Component

/-!
# Monomials in finite shifted coefficient modules

A monomial presentation on an exponent group restricts to a translate of any
submonoid. With positive degree data its relative truncations have bases indexed
by the retained relative degrees. These are presentations on the actual quotient
carriers used by filtered actions, with their existing homogeneous pieces.
Cutoff transitions preserve retained monomials and kill the discarded
ones, without changing the scalar coordinates of surviving decorations.

The construction uses `MonomialPresentation.subfamily` and
`MonomialPresentation.quotient`, with `PositiveDegrees.shiftedQuotientGrading`
for the finite homogeneous pieces. In particular it applies to the ordinary and
twisted exponent presentations, including quantum coefficients over rings with
zero divisors. No nontriviality of the scalar ring is required.
-/

public noncomputable section

namespace Mei.MonomialPresentation

variable {R M Γ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

section AddCancelCommMonoid

variable [AddCancelCommMonoid Γ] {ℳ : Γ → Submodule R M} (P : MonomialPresentation ℳ)
  (S : AddSubmonoid Γ) (p : Γ)

/-- The monomials supported on `p + S`, indexed by their relative degrees in `S`. -/
def shifted : MonomialPresentation (fun n : S => shiftedGrading ℳ S p n) where
  basis := (P.subfamily (fun n : S => p + n)
    (fun _ _ h => Subtype.ext (add_left_cancel h))
    (shiftedSubmodule ℳ S p) (shiftedSubmodule_def ℳ S p)).basis
  grade_eq_span n := by
    rw [shiftedGrading_def]
    exact (P.subfamily (fun n : S => p + n)
      (fun _ _ h => Subtype.ext (add_left_cancel h))
      (shiftedSubmodule ℳ S p) (shiftedSubmodule_def ℳ S p)).grade_eq_span n

/-- A shifted basis vector is the original monomial at the translated exponent. -/
@[simp]
theorem coe_shifted_basis (n : S) :
    ((P.shifted S p).basis n : M) = P.basis (p + n) :=
  P.coe_subfamily_basis _ _ _ _ n

/-- Shifted scalar coordinates are the ambient coordinates at translated exponents. -/
@[simp]
theorem shifted_repr (x : shiftedSubmodule ℳ S p) (n : S) :
    (P.shifted S p).basis.repr x n = P.basis.repr (x : M) (p + n) :=
  P.subfamily_repr _ _ _ _ x n

end AddCancelCommMonoid

variable [AddCommGroup Γ] {ℳ : Γ → Submodule R M} (P : MonomialPresentation ℳ)
  [DecidableEq Γ] [DirectSum.Decomposition ℳ]

/-- A relative filtration term discards exactly the shifted coordinates below its order. -/
theorem mem_shiftedFiltration_iff (d : PositiveDegrees Γ) (p : Γ) (k : ℕ)
    (x : shiftedSubmodule ℳ d.monoid p) :
    x ∈ (d.shiftedFiltration ℳ p).submodule k ↔
      ∀ n : d.monoid, d.degree n < k → (P.shifted d.monoid p).basis.repr x n = 0 := by
  rw [d.mem_shiftedFiltration_iff ℳ p]
  constructor
  · intro hx n hn
    have h := hx (p + n) (by simpa using hn)
    rw [P.coe_decompose] at h
    rw [shifted_repr]
    exact P.basis.linearIndependent.smul_left_injective (p + n) (by simpa using h)
  · intro hx q hq
    by_cases hqp : q - p ∈ d.monoid
    · have h := hx ⟨q - p, hqp⟩ (by simpa using hq)
      simp only [shifted_repr, add_sub_cancel] at h
      rw [P.coe_decompose, h, zero_smul]
    · exact (Mei.mem_shiftedSubmodule_iff ℳ d.monoid p).mp x.property q hqp

end Mei.MonomialPresentation

namespace Mei.MonomialPresentation

variable {R M : Type*} {Γ : Type} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {ℳ : Γ → Submodule R M}
  [DirectSum.Decomposition ℳ] (P : MonomialPresentation ℳ)
  (d : PositiveDegrees Γ) (p : Γ)

private theorem shiftedQuotient_coordinate_condition (k : ℕ)
    (x : shiftedSubmodule ℳ d.monoid p) :
    x ∈ (d.shiftedFiltration ℳ p).submodule (k + 1) ↔
      ∀ n ∈ {n : d.monoid | d.degree n ≤ k},
        (P.shifted d.monoid p).basis.repr x n = 0 := by
  rw [P.mem_shiftedFiltration_iff d p]
  exact forall_congr' fun n => imp_congr_left (by simp only [Set.mem_ofPred_eq]; omega)

/-- The actual shifted quotient, presented by the retained relative monomials. -/
def shiftedQuotient (k : ℕ) :
    MonomialPresentation (fun n : {n : d.monoid // d.degree n ≤ k} =>
      (d.shiftedQuotientGrading ℳ p k).piece n) where
  basis := ((P.shifted d.monoid p).quotient
    ((d.shiftedFiltration ℳ p).submodule (k + 1))
    {n | d.degree n ≤ k} (P.shiftedQuotient_coordinate_condition d p k)).basis
  grade_eq_span n := by
    rw [d.shiftedQuotientGrading_piece]
    exact ((P.shifted d.monoid p).quotient
      ((d.shiftedFiltration ℳ p).submodule (k + 1))
      {n | d.degree n ≤ k} (P.shiftedQuotient_coordinate_condition d p k)).grade_eq_span n

/-- A retained quotient monomial is the class of its shifted monomial. -/
@[simp]
theorem shiftedQuotient_basis (k : ℕ) (n : {n : d.monoid // d.degree n ≤ k}) :
    (P.shiftedQuotient d p k).basis n =
      Submodule.Quotient.mk ((P.shifted d.monoid p).basis n.val) :=
  (P.shifted d.monoid p).quotient_basis
    ((d.shiftedFiltration ℳ p).submodule (k + 1)) {n | d.degree n ≤ k}
    (P.shiftedQuotient_coordinate_condition d p k) n

/-- The finite scalar coordinate of a representative is its ambient monomial coordinate. -/
@[simp]
theorem shiftedQuotient_repr_mk (k : ℕ) (x : shiftedSubmodule ℳ d.monoid p)
    (n : {n : d.monoid // d.degree n ≤ k}) :
    (P.shiftedQuotient d p k).basis.repr (Submodule.Quotient.mk x) n =
      P.basis.repr (x : M) (p + n.val) := by
  exact ((P.shifted d.monoid p).quotient_repr_mk
    ((d.shiftedFiltration ℳ p).submodule (k + 1)) {n | d.degree n ≤ k}
    (P.shiftedQuotient_coordinate_condition d p k) x n).trans (P.shifted_repr _ _ x _)

/-- Each finite homogeneous component is its entire scalar coordinate times the
ambient monomial. This applies in particular to outputs of finite shifted actions. -/
theorem coe_shiftedQuotientComponent (k : ℕ)
    (x : (d.shiftedFiltration ℳ p).quotient k)
    (n : {n : d.monoid // d.degree n ≤ k}) :
    (d.shiftedQuotientComponent ℳ p (p + n.val) k (by simpa using n.property) x : M) =
      (P.shiftedQuotient d p k).basis.repr x n • P.basis (p + n.val) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  simp only [Submodule.mkQ_apply, d.shiftedQuotientComponent_mk,
    shiftedQuotient_repr_mk, P.coe_decompose]

/-- Reading a retained coordinate at any cutoff recovers the corresponding whole
homogeneous decoration of a completed shifted coefficient. -/
theorem coe_shiftedHomogeneousComponent (k : ℕ) (x : d.ShiftedCoefficients ℳ p)
    (n : {n : d.monoid // d.degree n ≤ k}) :
    (d.shiftedHomogeneousComponent ℳ p (p + n.val) x : M) =
      (P.shiftedQuotient d p k).basis.repr ((d.shiftedFiltration ℳ p).projection k x) n •
        P.basis (p + n.val) := by
  rw [d.shiftedHomogeneousComponent_eq ℳ p (p + n.val) k (by simpa using n.property)]
  exact P.coe_shiftedQuotientComponent d p k _ n

/-- A shifted monomial above the cutoff vanishes in the finite quotient. Together
with the basis-class rule, this computes every discarded cutoff transition. -/
@[simp]
theorem mk_shifted_basis_eq_zero (k : ℕ) (n : d.monoid) (hn : (k : ℤ) < d.degree n) :
    (Submodule.Quotient.mk ((P.shifted d.monoid p).basis n) :
      (d.shiftedFiltration ℳ p).quotient k) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, P.mem_shiftedFiltration_iff d p]
  intro m hm
  have hne : n ≠ m := by
    intro he
    rw [← he] at hm
    omega
  simp [Module.Basis.repr_self, hne]

/-- Cutoff transitions leave all surviving scalar coordinates unchanged. -/
@[simp]
theorem shiftedQuotient_repr_transition {k l : ℕ} (h : k ≤ l)
    (x : (d.shiftedFiltration ℳ p).quotient l)
    (n : {n : d.monoid // d.degree n ≤ k}) :
    (P.shiftedQuotient d p k).basis.repr ((d.shiftedFiltration ℳ p).transition h x) n =
      (P.shiftedQuotient d p l).basis.repr x ⟨n.val, n.property.trans (by exact_mod_cast h)⟩ := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  simp

end Mei.MonomialPresentation
