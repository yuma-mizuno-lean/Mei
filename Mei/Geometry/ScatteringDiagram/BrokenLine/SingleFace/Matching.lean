/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Resolution
public import Mei.Algebra.Category.SemimoduleCat.Multispan.Span

/-!
# Matching families of single-face ray evaluations

The span of a graded correspondence between two copies of a decomposed chamber module is the
incidence diagram of one face. The actual incoming and opposite-side ray sums, for a linear
family of admissible homogeneous inputs, are the chamber values of a unique linear family of
matching sections of that diagram, whose face component is a common linear lift of them. The
arrangement away from which the opposite side is generic is independent of the incoming
coefficient, and finitely generated incoming ranges give the finite-input test.

Graph and slab correspondences are instances; neither the legs separately nor the propagation
need be invertible, and only the joint injectivity of the span is used. This is matching at one
face. It does not supply the closed global family, the certificates across singular
degenerations, or descent along the stratification. The face matching follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
§3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory Limits Set

universe u

namespace Mei.GradedCorrespondence

variable {R V H Γ : Type*} {M B : Type u} [Semiring R]
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

/-- The incoming and opposite-side ray sums are the chamber values of a unique linear family of
matching sections of the face, uniformly over the incoming coefficient. The opposite endpoint
is generic for one exceptional arrangement chosen before the coefficient. -/
theorem existsUnique_singleFace_matchingFamily
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
      ∃! ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule
          (MultispanIndex.ofLinearMaps C.left C.right).multispan, ∀ x,
        (ℓ x).val (.right false) = ev(0, x, Q₀) ∧ (ℓ x).val (.right true) = ev(1, x, Q₁) := by
  obtain ⟨E, hE⟩ := C.existsUnique_singleFace_evaluation_lift p α v ν b Z hinj s hs hnormal hZ
    A hcover hA
  exact ⟨E, fun Q₀ Q₁ h₀ h₁ h₂ =>
    (MultispanIndex.existsUnique_sections_ofLinearMaps_iff C.left C.right _ _).mpr
      (hE Q₀ Q₁ h₀ h₁ h₂)⟩

/-- Every linear family with finitely generated incoming range has matching sections whose
chamber values are the incoming and opposite-side ray sums. This is the finite-input test; the
homogeneous pieces and the chamber module need not be finitely generated. -/
theorem existsUnique_singleFace_matchingFamily_of_fg
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
      ∃! ℓ : H →ₗ[R] SemimoduleCat.sectionsSubmodule
          (MultispanIndex.ofLinearMaps C.left C.right).multispan, ∀ x,
        (ℓ x).val (.right false) = ev(0, x, Q₀) ∧ (ℓ x).val (.right true) = ev(1, x, Q₁) := by
  obtain ⟨E, hE⟩ := C.existsUnique_singleFace_evaluation_lift_of_fg p α v ν b Z hinj hα hnormal hZ
    A hcover hA
  exact ⟨E, fun Q₀ Q₁ h₀ h₁ h₂ =>
    (MultispanIndex.existsUnique_sections_ofLinearMaps_iff C.left C.right _ _).mpr
      (hE Q₀ Q₁ h₀ h₁ h₂)⟩

end Mei.GradedCorrespondence
