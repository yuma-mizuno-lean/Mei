/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Component
public import Mei.LinearAlgebra.GradedModule.History.Uniform
public import Mei.LinearAlgebra.GradedCorrespondence.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Common lifts of single-face ray evaluations

For a graded correspondence between two copies of a decomposed chamber module,
propagation is its total transfer. A linear family of admissible homogeneous
inputs has the chosen face lift. One exceptional arrangement makes its two
chamber images equal to the actual incoming and opposite-side ray sums for all
inputs simultaneously. Joint injectivity makes this common linear lift unique.

Uniform finite output support is sufficient; finite generation of the incoming
range supplies it by the shared homogeneous-history expansion. This includes
every finite-input test, without requiring the homogeneous pieces or the chamber
module to be finitely generated. The incoming region is the full
half-space; rays with unchanged degrees or spatial velocities remain included.
Reversing the correspondence gives the same assertion for right-hand inputs.
Graph and slab correspondences use the same construction, with no invertibility
assumption on propagation or on either face map separately.

This supplies the terminal common-lift identity at one face. Closed-family
boundary comparisons and gluing of sections are separate constructions.
The terminal-face interpretation follows Gross–Hacking–Siebert, *Theta functions
on varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set

namespace Mei.GradedCorrespondence

variable {R M Γ V H B : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [DecidableEq Γ]
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [AddCommMonoid B] [Module R B] {I J : Set Γ}
  (C : GradedCorrespondence (B := B) ℳ ℳ I J)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommMonoid H] [Module R H]
  (p : I) (α : H →ₗ[R] ℳ p) (v : Γ → V)
  (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)

local notation "ev(" n ", " x ", " Q ")" =>
  decoratedRayEvaluation ℳ (fun _ : Fin n => C.totalTransfer) p (α x) v
    (fun _ => ν) (fun _ => b) (fun _ => SignType.sign (ν (v p)))
    (fun _ => Set.ofPred (fun x => ν x = b)) (fun _ : Unit => Set.ofPred (fun x => ν x = b))
    (fun _ : Unit => Z) (Set.ofPred (fun x => 0 < (ν x - b) / ν (v p))) Q

/-- One arrangement identifies the two actual ray sums with the images of the
chosen face lift, uniformly over the incoming linear family. Only the output
components of that family need to preserve normal velocity. -/
theorem exists_singleFace_evaluation_lift_arrangement
    (s : Finset Γ) (hs : ∀ x q, C.transfer p q (α x) ≠ 0 → q ∈ s)
    (hnormal : ∀ x q, C.transfer p q (α x) ≠ 0 → ν (v q) = ν (v p))
    (hZ : Z ⊆ {x | ν x = b})
    {κ : Type*} [Finite κ] (A : κ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ E : ExceptionalArrangement V,
      (∀ Q, 0 < (ν Q - b) / ν (v p) → ∀ x,
        C.left ((C.liftLeft p).comp α x) = ev(0, x, Q)) ∧
      (∀ Q, E.IsGeneric Q → (ν Q - b) / ν (v p) < 0 → ∀ x,
        C.right ((C.liftLeft p).comp α x) = ev(1, x, Q)) := by
  have hT (x : H) : C.totalTransfer (α x) = C.right (C.liftLeft p (α x)) := by
    rw [totalTransfer_apply, liftLeftTotal_coe]
  have hn (x : H) (q : Γ) : DirectSum.decompose ℳ (C.totalTransfer (α x)) q ≠ 0 →
      ν (v q) = ν (v p) := by
    rw [hT, ← transfer_apply]
    exact hnormal x q
  have hsupport (x : H) (q : Γ) :
      DirectSum.decompose ℳ (C.totalTransfer (α x)) q ≠ 0 → q ∈ s := by
    rw [hT, ← transfer_apply]
    exact hs x q
  obtain ⟨E, hE⟩ := exists_uniform_decoratedRayEvaluation_singleFace_arrangement
    ℳ C.totalTransfer p v ν b Z hZ α hn s hsupport A hcover hA
  refine ⟨E, ?_, fun Q hQ ht x => (hT x).symm.trans (hE Q hQ ht x).symm⟩
  intro Q hQ x
  rw [LinearMap.comp_apply, left_liftLeft_apply,
    decoratedRayEvaluation_singleFace_empty ℳ C.totalTransfer p (α x) v ν b Z hZ Q,
    ite_eq_left hQ]

/-- At any incoming endpoint and any generic opposite-side endpoint, the actual
ray sums admit exactly one common linear face lift. The same arrangement works
for every incoming coefficient, including zero and cancelling combinations. -/
theorem existsUnique_singleFace_evaluation_lift
    (hinj : Function.Injective (C.left.prod C.right))
    (s : Finset Γ) (hs : ∀ x q, C.transfer p q (α x) ≠ 0 → q ∈ s)
    (hnormal : ∀ x q, C.transfer p q (α x) ≠ 0 → ν (v q) = ν (v p))
    (hZ : Z ⊆ {x | ν x = b})
    {κ : Type*} [Finite κ] (A : κ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ E : ExceptionalArrangement V, ∀ Q₀ Q₁,
      0 < (ν Q₀ - b) / ν (v p) → E.IsGeneric Q₁ →
      (ν Q₁ - b) / ν (v p) < 0 →
      ∃! ℓ : H →ₗ[R] B, ∀ x,
        C.left (ℓ x) = ev(0, x, Q₀) ∧ C.right (ℓ x) = ev(1, x, Q₁) := by
  obtain ⟨E, hleft, hright⟩ := C.exists_singleFace_evaluation_lift_arrangement
    p α v ν b Z s hs hnormal hZ A hcover hA
  refine ⟨E, fun Q₀ Q₁ hQ₀ hQ₁ ht =>
    ⟨(C.liftLeft p).comp α, fun x => ⟨hleft Q₀ hQ₀ x, hright Q₁ hQ₁ ht x⟩, ?_⟩⟩
  intro ℓ hℓ
  apply LinearMap.ext
  intro x
  apply hinj
  exact Prod.ext ((hℓ x).1.trans (hleft Q₀ hQ₀ x).symm)
    ((hℓ x).2.trans (hright Q₁ hQ₁ ht x).symm)

/-- Every linear family with finitely generated incoming range satisfies the
uniform terminal common-lift identity. This gives the finite-input test without
requiring any finiteness of the ambient grading or its homogeneous pieces. -/
theorem existsUnique_singleFace_evaluation_lift_of_fg
    (hinj : Function.Injective (C.left.prod C.right))
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ x q, C.transfer p q (α x) ≠ 0 → ν (v q) = ν (v p))
    (hZ : Z ⊆ {x | ν x = b})
    {κ : Type*} [Finite κ] (A : κ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ E : ExceptionalArrangement V, ∀ Q₀ Q₁,
      0 < (ν Q₀ - b) / ν (v p) → E.IsGeneric Q₁ →
      (ν Q₁ - b) / ν (v p) < 0 →
      ∃! ℓ : H →ₗ[R] B, ∀ x,
        C.left (ℓ x) = ev(0, x, Q₀) ∧ C.right (ℓ x) = ev(1, x, Q₁) := by
  classical
  have hfg : (LinearMap.range ((ℳ p).subtype.comp α)).FG := by
    rw [LinearMap.range_comp]
    exact hα.map _
  obtain ⟨S, hS⟩ := exists_uniform_homogeneousHistory_support ℳ
    (fun _ : Fin 1 => C.totalTransfer) ((ℳ p).subtype.comp α) hfg
  apply C.existsUnique_singleFace_evaluation_lift p α v ν b Z hinj
    (S.image fun r => r 0) ?_ hnormal hZ A hcover hA
  intro x q hq
  apply Finset.mem_image.mpr
  refine ⟨fun _ => q, ?_, rfl⟩
  by_contra hs
  have hz := LinearMap.congr_fun (hS (fun _ => q) hs) x
  have he : (C.transfer p q (α x) : M) = 0 := by
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      homogeneousHistory_succ_apply, homogeneousHistory_zero, LinearMap.id_apply,
      totalTransfer_apply, liftLeftTotal_coe, transfer_apply] using hz
  exact hq (Subtype.val_injective he)

end Mei.GradedCorrespondence
