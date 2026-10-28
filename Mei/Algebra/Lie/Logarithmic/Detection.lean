/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Detecting logarithmic fields on coefficient monomials

A monomial test recovers each formal character evaluated on its spatial exponent.
Consequently tests whose spatial exponents span the rationalized tangent group
determine a formal field. In a positively graded tangent algebra, a field surviving
a given cutoff has a nonzero monomial observation in a Lie degree at or below it.
This supplies the coefficient detection needed for faithful completed actions.

The coefficient calculation `LogarithmicVectorField.action_coeff` follows
`LogarithmicVectorField.realization_coeff`. Detection uses Mathlib's
`LinearMap.liftBaseChange` and the universal property of linear span.
The faithfulness question comes from Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

open _root_.AddMonoidAlgebra
open scoped TensorProduct

namespace Mei.LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [AddCancelCommMonoid Γ]

section Rational

variable [AddCommGroup Λ] [Algebra ℚ R] (ρ : Γ →+ Λ) (P : Set Γ)
  (hspan : Submodule.span ℚ ((fun p : Γ => (1 : ℚ) ⊗ₜ[ℤ] ρ p) '' P) = ⊤)

include hspan

/-- Every nonzero formal character is observed on some monomial whose spatial
exponent belongs to a rationally spanning test family. -/
theorem exists_action_apply_single_coeff_ne_zero (x : LogarithmicVectorField R Γ Λ ρ)
    {n : Γ} (hn : toFinsupp ρ x n ≠ 0) :
    ∃ p ∈ P, (action ρ x (_root_.AddMonoidAlgebra.single p 1)).coeff (n + p) ≠ 0 := by
  by_contra h
  push Not at h
  let f := (toFinsupp ρ x n).toIntLinearMap.liftBaseChange ℚ
  have hf : f = 0 := LinearMap.ext_on hspan (by rintro _ ⟨p, hp, rfl⟩; simpa [f] using h p hp)
  apply hn
  ext l
  simpa [f] using LinearMap.congr_fun hf ((1 : ℚ) ⊗ₜ[ℤ] l)

/-- Monomial tests with rationally spanning spatial exponents determine a formal field.
The test outputs remain in the ambient monoid algebra. -/
theorem action_apply_single_injective : Function.Injective
    (fun x : LogarithmicVectorField R Γ Λ ρ =>
      fun p : P => action ρ x (_root_.AddMonoidAlgebra.single p.val 1)) := by
  intro x y h
  apply (toFinsupp ρ).injective
  ext n l
  have hz : toFinsupp ρ (x - y) n = 0 := by
    by_contra hn
    obtain ⟨p, hp, hne⟩ := exists_action_apply_single_coeff_ne_zero ρ P hspan (x - y) hn
    have he := congrFun h ⟨p, hp⟩
    apply hne
    simp only [map_sub, Derivation.sub_apply, he, sub_self]
    simp
  have he := DFunLike.congr_fun hz l
  have he' : toFinsupp ρ x n l - toFinsupp ρ y n l = 0 := by simpa using he
  exact sub_eq_zero.mp he'

end Rational
end Mei.LogarithmicVectorField

namespace Mei

open LogarithmicVectorField

variable {R Γ Λ : Type*} [CommRing R] [Algebra ℚ R]
  [AddCancelCommMonoid Γ] [AddCommGroup Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)
  (hspan : Submodule.span ℚ
    ((fun p : Γ => (1 : ℚ) ⊗ₜ[ℤ] ρ p) '' (d.monoid : Set Γ)) = ⊤)

include hspan

/-- If the spatial exponents of `d.monoid` span `ℚ ⊗[ℤ] Λ`, then a positive tangent
field with a nonzero homogeneous component of degree at most `k` (that is, not in
`degreeSubmodule k`) has a nonzero monomial coefficient at a nonzero positive degree
`n` with `d.degree n ≤ k`, tested on some `p ∈ d.monoid`. -/
theorem exists_action_apply_single_coeff_ne_zero_of_notMem_degreeSubmodule
    {k : ℕ} (x : tropicalVertexLieAlgebra (R := R) d ρ)
    (hx : x ∉ d.degreeSubmodule (tropicalVertexGrading d ρ) k) :
    ∃ n ∈ d.monoid, n ≠ 0 ∧ d.degree n ≤ k ∧
      ∃ p ∈ d.monoid,
        (action ρ x.val (_root_.AddMonoidAlgebra.single p 1)).coeff (n + p) ≠ 0 := by
  classical
  have hx' : x.val ∉ d.degreeSubmodule (grade (R := R) ρ) k := by
    intro h
    apply hx
    rw [d.degreeSubmodule_comap (grade (R := R) ρ) (tropicalVertexGrading d ρ)
      (tropicalVertexLieAlgebra d ρ).incl.toLinearMap Subtype.val_injective
      (fun _ _ h => by simpa only [tropicalVertexGrading_def, Submodule.mem_comap] using h)]
    exact h
  rw [d.mem_degreeSubmodule_iff] at hx'
  push Not at hx'
  obtain ⟨n, hnk, hn⟩ := hx'
  have hc : toFinsupp ρ x.val n ≠ 0 := by
    intro h
    rw [decompose_grade, h, map_zero] at hn
    exact hn rfl
  have hpos : n ∈ d.monoid ∧ n ≠ 0 := by
    by_contra h
    exact hc ((mem_tropicalVertexLieAlgebra_iff d ρ x.val).mp x.property |>.2 n (by tauto))
  obtain ⟨p, hp, hne⟩ :=
    exists_action_apply_single_coeff_ne_zero ρ (d.monoid : Set Γ) hspan x.val hc
  exact ⟨n, hpos.1, hpos.2, hnk, p, hp, hne⟩

end Mei
