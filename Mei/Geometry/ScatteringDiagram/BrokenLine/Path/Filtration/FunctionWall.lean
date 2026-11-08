/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Filtration
public import Mei.RingTheory.GradedAlgebra.FunctionWall.Filtration
public import Mei.RingTheory.FilteredAlgebra.Module

/-!
# Encounter bounds for nilpotent function walls along quiver paths

Let every arrow of a finite quiver act on a common graded commutative ring by a
function wall congruent to one modulo a homogeneous nilpotent ideal. Degree-preserving
components preserve ideal order, while degree-changing components raise it. If the
velocity of a degree does not depend on the chamber, every actual decorated ray along
any encounter path has at most `r` times the number of arrows encounters, where the
`r`th power of the ideal vanishes. No positivity or finite cutoff of the exponent
grading is required.

We combine `functionWallAction_mem_pow` and `decompose_functionWallAction_mem_pow_succ`
with `PathDecoratedRay.length_le_of_filtration`. Negative normal weights, zero divisors,
unchanged-degree encounters and changes of degree with zero spatial displacement remain
allowed. This is the ordinary-wall part of Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4).
-/

public noncomputable section

open Quiver Mei.GradedAlgebra

namespace Mei.PathDecoratedRay

variable {Q R A Γ V J K : Type*} [Quiver Q] [Finite (Σ b c : Q, b ⟶ c)]
  [CommSemiring R] [CommRing A] [Algebra R A] [AddMonoid Γ] [DecidableEq Γ]
  (𝒢 : Γ → Submodule R A) [GradedAlgebra 𝒢]
  (𝒜 : ∀ {b c : Q}, (b ⟶ c) → ℤ → Submodule R A)
  [∀ {b c : Q} (e : b ⟶ c), GradedAlgebra (𝒜 e)]
  (θ : ∀ {b c : Q} (e : b ⟶ c), (𝒜 e 0)ˣ) (weight : ∀ {b c : Q}, (b ⟶ c) → Γ → ℤ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {a b : Q} {i₀ : Γ} {x : 𝒢 i₀} {v : Q → Γ → V}
  {ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ} {ε : ∀ {b c : Q}, (b ⟶ c) → SignType}
  {c : ∀ {b c : Q}, (b ⟶ c) → ℝ} {P : ∀ {b c : Q}, (b ⟶ c) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {p : Path a b} {X : V}

/-- Nilpotent function walls bound all encounters of an actual decorated ray along
any encounter path, without assuming an encounter bound or a positive ordering of
the exponent degrees. The same bound works at every endpoint and for every input. -/
theorem length_le_of_functionWallAction
    (β : PathDecoratedRay (M := fun _ => A) (ι := fun _ => Γ)
      (fun e => (functionWallAction (𝒜 e) (θ e)).toLinearMap) (fun _ => 𝒢)
      i₀ x v ν ε c P W S C p X)
    (I : Ideal A) (hI : I.IsHomogeneous 𝒢)
    (hθ : ∀ {b c : Q} (e : b ⟶ c), algebraMap (𝒜 e 0) A (θ e) - 1 ∈ I)
    (hw : ∀ {b c : Q} (e : b ⟶ c) q, 𝒢 q ≤ 𝒜 e (weight e q))
    (hv : ∀ {b c : Q} (_ : b ⟶ c) (i : Γ), v b i = v c i) {r : ℕ} (hr : I ^ r = ⊥) :
    p.length ≤ r * Nat.card (Σ b c : Q, b ⟶ c) := by
  apply β.length_le_of_filtration
    (F := fun _ => (AlgFiltration.ofIdeal I).toModuleFiltration R)
    (mark := fun _ i j => if i = j then 0 else 1)
  · rw [componentTransfersRaise_iff]
    intro b c e i j k y hy hpow
    rw [AlgFiltration.toModuleFiltration_submodule, AlgFiltration.ofIdeal_ideal,
      Submodule.restrictScalars_mem] at hpow ⊢
    by_cases hij : i = j
    · simp only [hij, ite_true, Nat.add_zero]
      simpa only [homogeneousComponent_apply, AlgEquiv.toLinearMap_apply] using
        ((hI.pow k).mem_iff.mp
          (functionWallAction_mem_pow (𝒜 e) I (θ e) (hw e i hy) hpow)) j
    · simp only [hij, ite_false]
      simpa only [homogeneousComponent_apply, AlgEquiv.toLinearMap_apply] using
        decompose_functionWallAction_mem_pow_succ (𝒜 e) I 𝒢 hI (θ e)
          (hθ e) (hw e i hy) hpow hy hij
  · intro b c e i j h
    by_cases hij : i = j
    · rw [← hij]
      exact hv e i
    · simp [hij] at h
  · simp only [AlgFiltration.ofIdeal_ideal, hr, Submodule.restrictScalars_bot]

end Mei.PathDecoratedRay
