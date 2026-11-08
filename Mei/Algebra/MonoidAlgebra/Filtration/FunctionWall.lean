/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Filtration.Coefficient
public import Mei.RingTheory.GradedAlgebra.FunctionWall.Filtration

/-!
# Coefficient filtration of ordinary function walls

The coefficient-ideal filtration of a monoid algebra agrees with the powers of
the extended scalar ideal. Consequently the ideal-order estimates for function
walls apply to the same filtration as slab transfers: components preserving the
exponent preserve order, and other components raise it. This comparison permits
ordinary walls and slab faces to occur in one propagation history.

The estimate uses `decompose_functionWallAction_mem_pow_succ`, including negative
normal weights. Its geometric application is the nilpotent-ideal finiteness
argument of Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.GradedAlgebra

open AddMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommMonoid Γ] [DecidableEq Γ]
  (𝒜 : ℤ → Submodule R R[Γ]) [GradedAlgebra 𝒜]
  (I : Ideal R) (θ : (𝒜 0)ˣ)

/-- A function wall congruent to one modulo the extended scalar ideal obeys
the coefficient-filtration estimate used by slab transfers. The normal weight
may be positive, zero or negative. -/
theorem homogeneousComponent_functionWallAction_mem_coeffFiltration
    (hθ : algebraMap (𝒜 0) R[Γ] θ - 1 ∈ I.map (algebraMap R R[Γ]))
    {p q : Γ} {x : R[Γ]} (hx : x ∈ grade R p)
    {m : ℤ} (hm : x ∈ 𝒜 m) {k : ℕ}
    (hk : x ∈ (I.coeffFiltration Γ).submodule k) :
    homogeneousComponent (grade R) q (functionWallAction 𝒜 θ x) ∈
      (I.coeffFiltration Γ).submodule (k + if p = q then 0 else 1) := by
  have hI := I.isHomogeneous_map_algebraMap_grade Γ
  have hxk : x ∈ (I.map (algebraMap R R[Γ])) ^ k := by
    simpa only [Ideal.coeffFiltration_submodule_eq_restrictScalars_map_pow,
      Submodule.restrictScalars_mem] using hk
  rw [homogeneousComponent_apply,
    Ideal.coeffFiltration_submodule_eq_restrictScalars_map_pow, Submodule.restrictScalars_mem]
  by_cases hpq : p = q
  · simp only [hpq, ite_true, Nat.add_zero]
    exact ((hI.pow k).mem_iff.mp (functionWallAction_mem_pow 𝒜 _ θ hm hxk)) q
  · simp only [hpq, ite_false]
    exact decompose_functionWallAction_mem_pow_succ 𝒜 _ (grade R) hI θ hθ hm hxk hx hpq

end Mei.GradedAlgebra
