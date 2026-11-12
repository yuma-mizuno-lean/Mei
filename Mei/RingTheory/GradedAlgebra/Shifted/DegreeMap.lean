/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.Basic

/-!
# Products under changes of coefficient degrees

A multiplicative homogeneous linear map preserves products of completed shifted
coefficients. Its degree map may merge degrees, and its cutoff modulus need not
be the identity. The result specializes intertwining of completed bilinear maps.
This is the coefficient setting of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace TauCeti.PositiveDegreeMap

open Mei

variable {Γ Γ' R A B : Type*} [AddCommGroup Γ] [AddCommGroup Γ']
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [DecidableEq Γ] {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  (T : PositiveDegreeMap d e) (𝒜 : Γ → Submodule R A) (ℬ : Γ' → Submodule R B)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] [SetLike.GradedMul ℬ]
  (f : A →ₗ[R] B) (hf : ∀ n, 𝒜 n ≤ (ℬ (T n)).comap f)

/-- Degree-changing coefficient maps preserve products after identifying the sum of shifts. -/
theorem shiftedCompletionMap_mul (hmul : ∀ a b, f (a * b) = f a * f b)
    (p q : Γ) (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    cast (congrArg (e.ShiftedCoefficients ℬ) (_root_.map_add T.toAddMonoidHom p q))
      (T.shiftedCompletionMap 𝒜 ℬ (p + q) f hf (d.shiftedCompletionMul 𝒜 p q x y)) =
    e.shiftedCompletionMul ℬ (T p) (T q)
      (T.shiftedCompletionMap 𝒜 ℬ p f hf x) (T.shiftedCompletionMap 𝒜 ℬ q f hf y) := by
  simp only [shiftedCompletionMap_def, PositiveDegrees.shiftedCompletionMul_def]
  rw [e.cast_completionMap ℬ (h := _root_.map_add T.toAddMonoidHom p q)]
  apply ModuleFiltration.completionMap_completionBilinear
  intro a b
  apply Subtype.ext
  have hcast (s t : Γ') (h : s = t)
      (g : shiftedSubmodule 𝒜 d.monoid (p + q) →ₗ[R] shiftedSubmodule ℬ e.monoid s)
      (z : shiftedSubmodule 𝒜 d.monoid (p + q)) :
      ((h ▸ g) z : B) = (g z : B) := by subst t; rfl
  rw [hcast _ _ (_root_.map_add T.toAddMonoidHom p q)]
  simp only [coe_shiftedMap, coe_shiftedMul, hmul]

end TauCeti.PositiveDegreeMap
