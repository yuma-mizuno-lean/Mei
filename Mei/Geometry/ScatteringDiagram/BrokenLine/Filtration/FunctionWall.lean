/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.EncounterBound
public import Mei.RingTheory.GradedAlgebra.FunctionWall.Filtration
public import Mei.RingTheory.FilteredAlgebra.Module

/-!
# Encounter bounds for nilpotent function walls

Function walls congruent to one modulo a homogeneous nilpotent ideal give a
uniform bound on every actual decorated-ray encounter word. Degree-preserving
components preserve ideal order and spatial direction, while degree-changing
components raise ideal order. Thus the full word has length at most
`r * Nat.card J` when the ideal's `r`th power vanishes. No positivity or finite
cutoff of the exponent grading is required.

We combine `functionWallAction_mem_pow` and
`decompose_functionWallAction_mem_pow_succ` with the geometric component-filtration
bound. Negative normal weights, zero divisors, unchanged-degree encounters and
changes of degree with zero spatial displacement remain allowed. This is the
ordinary-wall part of Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.DecoratedAdmissibleRay

open Mei.GradedAlgebra

variable {R A Γ V J K O : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]
  (𝒢 : Γ → Submodule R A) [GradedAlgebra 𝒢]
  (𝒜 : J → ℤ → Submodule R A) [∀ e, GradedAlgebra (𝒜 e)]
  (θ : ∀ e, (𝒜 e 0)ˣ) (weight : J → Γ → ℤ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {n : ℕ} {p₀ : Γ} {a : 𝒢 p₀} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : O → Set V} {S : K → Set V} {C : Set V} {Q : V}
  {wall : Fin n → J}

/-- Nilpotent function walls bound all encounters of an actual decorated ray,
without assuming an encounter bound or a positive ordering of its exponent
degrees. The same bound works at every endpoint and for every incoming input. -/
theorem encounter_count_le_of_functionWallAction
    (β : DecoratedAdmissibleRay 𝒢
      (fun j => (functionWallAction (𝒜 (wall j)) (θ (wall j))).toLinearMap)
      p₀ a v (fun j => f (wall j)) (fun j => c (wall j)) (fun j => ε (wall j))
      (fun j => P (wall j)) W S C Q)
    (I : Ideal A) (hI : I.IsHomogeneous 𝒢)
    (hθ : ∀ e, algebraMap (𝒜 e 0) A (θ e) - 1 ∈ I)
    (hw : ∀ e q, 𝒢 q ≤ 𝒜 e (weight e q)) {r : ℕ} (hr : I ^ r = ⊥) :
    n ≤ r * Nat.card J := by
  apply encounter_count_le_of_filtration
    (T := fun e : J => (functionWallAction (𝒜 e) (θ e)).toLinearMap) (wall := wall) β
    ((AlgFiltration.ofIdeal I).toModuleFiltration R)
    (fun _ i j => if i = j then 0 else 1) ?_ ?_ ?_
  · intro e i j k x hx hpow
    rw [AlgFiltration.toModuleFiltration_submodule, AlgFiltration.ofIdeal_ideal,
      Submodule.restrictScalars_mem] at hpow ⊢
    by_cases hij : i = j
    · simp only [hij, ite_true, Nat.add_zero]
      simpa only [homogeneousComponent_apply, AlgEquiv.toLinearMap_apply] using
        ((hI.pow k).mem_iff.mp
          (functionWallAction_mem_pow (𝒜 e) I (θ e) (hw e i hx) hpow)) j
    · simp only [hij, ite_false]
      simpa only [homogeneousComponent_apply, AlgEquiv.toLinearMap_apply] using
        decompose_functionWallAction_mem_pow_succ (𝒜 e) I 𝒢 hI (θ e)
          (hθ e) (hw e i hx) hpow hx hij
  · intro e i j h
    by_cases hij : i = j
    · exact congrArg v hij
    · simp [hij] at h
  · simp only [AlgFiltration.ofIdeal_ideal, hr,
      Submodule.restrictScalars_bot]

end Mei.DecoratedAdmissibleRay
