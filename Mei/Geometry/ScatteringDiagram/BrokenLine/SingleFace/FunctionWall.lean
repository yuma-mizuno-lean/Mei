/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Evaluation
public import Mei.Algebra.DirectSum.Coarsening
public import Mei.RingTheory.GradedAlgebra.FunctionWall.Basic

/-!
# Weighted evaluation through a weight-preserving wall

Consider a single face `{ν = b}` whose wall maps preserve a coarser grading of the coefficient
module by weights, and suppose that the normal velocity `ν (v q)` of an exponent degree `q`
depends only on its weight `w q`. A component of the image of an element of weight `w 0` then has
weight `w 0`, hence the normal velocity of the incoming datum. The normal-velocity condition
of the single-face evaluation, which is the only condition on the velocities of the components,
is therefore automatic. On the far side of the face the weighted evaluation is the sum of the wall
images of the incoming coefficient over the walls of the matching crossing sign. The cutoff and
the singular set constrain only the components which occur.

Function walls are the main example. A function wall of a weight-zero unit `θ` acts on a
weight-graded algebra by `a ↦ a θ ^ w`, where `w` is the weight of `a`; this preserves weights, and
the weight of an exponent degree is the normal weight of the wall. The far-side evaluation is then
the incoming coefficient times the power `θ ^ w` of the wall function, summed over the walls
of the matching crossing sign. The exponent grading may be strictly finer than the weight grading.
Components of unchanged exponent degree, and components whose spatial velocity is unchanged or
changes within the face, all contribute. For the wall function `1 - z` and an incoming datum of
normal weight one, the far-side evaluation is `a - a z`.

The function-wall formula follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(i), and the single-face broken lines follow
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*, §3
(arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei

section WeightPreserving

variable {R M Γ V J κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [DecidableEq Γ]
  [DecidableEq κ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ] {d : PositiveDegrees Γ}
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V} {ε : J → SignType}
  {ν : V →L[ℝ] ℝ} {b : ℝ} {Z : Set V} {k : ℕ} {Q : V}

/-- Weighted evaluation through a face whose wall maps preserve a coarser weight grading `𝒜`
refined by `ℳ` along `w`. The normal velocity is assumed to depend only on the weight. On the far
side of the face the evaluation is the sum of the transfers `T j a` over the walls of the matching
crossing sign, provided that each of their components lies in the enumeration cutoff and crosses
the face outside the singular set `Z`. -/
theorem cutoffDecoratedEvaluation_singleFace_of_neg_of_weight [Fintype J]
    (𝒜 : κ → Submodule R M) [DirectSum.Decomposition 𝒜] (w : Γ → κ)
    (hw : ∀ q, ℳ q ≤ 𝒜 (w q)) (hT : ∀ j i x, x ∈ 𝒜 i → T j x ∈ 𝒜 i)
    (hν : ∀ q, w q = w 0 → ν (v q) = ν (v 0)) (hZ : Z ⊆ {x | ν x = b})
    (hQ : (ν Q - b) / ν (v 0) < 0)
    (hcut : ∀ j, SignType.sign (ν (v 0)) = ε j → ∀ η,
      DirectSum.decompose ℳ (T j a) η ≠ 0 → η ∈ d.cutoff k ∧
        Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z) :
    cutoffDecoratedEvaluation d ℳ T a v (fun _ : J => ν) (fun _ : J => b) ε
      (fun _ : J => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
      {x | 0 < (ν x - b) / ν (v 0)} k Q =
      ∑ j with SignType.sign (ν (v 0)) = ε j, (T j a : M) := by
  refine cutoffDecoratedEvaluation_singleFace_of_neg hZ hQ fun j hj η hη => ?_
  refine ⟨(hcut j hj η hη).1, hν η ?_, (hcut j hj η hη).2⟩
  by_contra hne
  exact hη (DirectSum.decompose_eq_zero_of_mem_of_le ℳ 𝒜 w (fun q x hx => hw q hx)
    (hT j _ _ (hw 0 a.2)) hne)

end WeightPreserving

section FunctionWall

open Mei.GradedAlgebra

variable {R A Γ V J : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [DecidableEq Γ]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {ℳ : Γ → Submodule R A}
  [DirectSum.Decomposition ℳ] [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ]
  {d : PositiveDegrees Γ} {a : ℳ 0} {v : Γ → V} {ε : J → SignType}
  {ν : V →L[ℝ] ℝ} {b : ℝ} {Z : Set V} {k : ℕ} {Q : V}

/-- Weighted evaluation through a face of function walls `θ j`, of weight `w q` on the exponent
degree `q`, which is its normal velocity. On the far side of the face the evaluation is the sum,
over the walls of the matching crossing sign, of the incoming coefficient times the power
`θ j ^ w 0` of the wall function, where `w 0` is the weight of the incoming datum. No condition
on the velocities of the components is needed, since the function walls preserve weights. -/
theorem cutoffDecoratedEvaluation_functionWall_of_neg [Fintype J] (θ : J → (𝒜 0)ˣ) (w : Γ → ℤ)
    (hw : ∀ q, ℳ q ≤ 𝒜 (w q)) (hν : ∀ q, ν (v q) = w q) (hZ : Z ⊆ {x | ν x = b})
    (hQ : (ν Q - b) / ν (v 0) < 0)
    (hcut : ∀ j, SignType.sign (ν (v 0)) = ε j → ∀ η,
      DirectSum.decompose ℳ (functionWallAction 𝒜 (θ j) a) η ≠ 0 → η ∈ d.cutoff k ∧
        Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z) :
    cutoffDecoratedEvaluation d ℳ (fun j => (functionWallAction 𝒜 (θ j)).toLinearMap) a v
        (fun _ : J => ν) (fun _ : J => b) ε (fun _ : J => {x | ν x = b})
        (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
        {x | 0 < (ν x - b) / ν (v 0)} k Q =
      ∑ j with SignType.sign (ν (v 0)) = ε j,
        (a : A) * algebraMap (𝒜 0) A ((θ j) ^ w 0 : (𝒜 0)ˣ) := by
  rw [cutoffDecoratedEvaluation_singleFace_of_neg_of_weight 𝒜 w hw
    (fun j _ _ hx => functionWallAction_mem 𝒜 (θ j) hx)
    (fun q hq => by rw [hν, hν, hq]) hZ hQ hcut]
  exact Finset.sum_congr rfl fun j _ => functionWallAction_apply_of_mem 𝒜 (θ j) (hw 0 a.2)

end FunctionWall

section OneWall

open Mei.GradedAlgebra

variable {R A Γ V : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq Γ]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] {ℳ : Γ → Submodule R A}
  [DirectSum.Decomposition ℳ] [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ]
  {d : PositiveDegrees Γ} {a : ℳ 0} {v : Γ → V} {ε : Unit → SignType}
  {ν : V →L[ℝ] ℝ} {b : ℝ} {k : ℕ} {Q : V}

/-- Weighted evaluation through one function wall `θ = 1 - z`, for an incoming datum `a` of
relative degree zero and normal weight `ν (v 0) = 1`. The wall multiplies `a` by `1 - z`, and
`a z` lies in the single exponent degree `n`. On the far side of the wall, with `n` in the
enumeration cutoff and no singular set, the evaluation is `a - a z`. On the source side it is `a`,
by `cutoffDecoratedEvaluation_singleFace_of_pos`. The weight `w 0` of `a` is one, so the wall acts
by the first power of `θ`; the weight of `n` is not constrained, since `a z` is zero unless
it equals the weight of `a`. -/
theorem cutoffDecoratedEvaluation_functionWall_one_sub_of_neg (θ : (𝒜 0)ˣ) (z : A) {n : Γ}
    (hθ : (θ : A) = 1 - z) (hz : (a : A) * z ∈ ℳ n) (hn : n ∈ d.cutoff k) (w : Γ → ℤ)
    (hw : ∀ q, ℳ q ≤ 𝒜 (w q)) (hν : ∀ q, ν (v q) = w q) (hν0 : ν (v 0) = 1)
    (hε : ε () = 1) (hQ : ν Q < b) :
    cutoffDecoratedEvaluation d ℳ (fun _ : Unit => (functionWallAction 𝒜 θ).toLinearMap) a v
        (fun _ : Unit => ν) (fun _ : Unit => b) ε (fun _ : Unit => {x | ν x = b})
        (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => (∅ : Set V))
        {x | 0 < (ν x - b) / ν (v 0)} k Q = (a : A) - a * z := by
  have hw0 : w 0 = 1 := by
    have := hν 0
    rw [hν0] at this
    exact_mod_cast this.symm
  have hap : functionWallAction 𝒜 θ a = (a : A) - a * z := by
    rw [functionWallAction_apply_of_mem 𝒜 θ (hw 0 a.2), hw0, zpow_one]
    simp [hθ, mul_sub]
  rw [cutoffDecoratedEvaluation_functionWall_of_neg 𝒜 (fun _ : Unit => θ) w hw hν
    (Set.empty_subset _) (by rwa [hν0, div_one, sub_neg]) ?_]
  · simp [hw0, hε, hν0, hθ, mul_sub]
  · intro j _ η hη
    refine ⟨?_, by simp⟩
    rw [hap, DirectSum.decompose_sub, DirectSum.decompose_of_mem ℳ a.2,
      DirectSum.decompose_of_mem ℳ hz] at hη
    by_cases h0 : η = 0
    · subst h0
      exact d.mem_cutoff.mpr ⟨d.monoid.zero_mem, by simp⟩
    · by_cases hn' : η = n
      · exact hn' ▸ hn
      · exact absurd (by
          rw [DirectSum.sub_apply, DirectSum.of_eq_of_ne _ _ _ h0,
            DirectSum.of_eq_of_ne _ _ _ hn', sub_zero]) hη

end OneWall

end Mei
