/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Family
public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace.Matching

/-!
# Matching sections of closed single-face transfer families

The weighted endpoint evaluation of the single-face transfer family is the
opposite chamber value of a unique matching section of its coefficient span.
For a linear incoming family with finitely generated range, one exceptional
arrangement works for every input. The face value is the total incoming lift;
individual outgoing branches do not need face lifts.

The characterization uses the actual endpoint family and its whole transfer
weights, including killed and cancelling inputs. The two chambers may carry
different semimodules and unrelated degree sets. The original half-space incoming
tails, singular exclusions and closed path extensions are those of
`singleFaceTransferFamily`; no singular boundary path is declared admissible.
This identifies the terminal matching data, rather than a section on the whole
base or a certificate across singular degenerations.

We combine the endpoint-family comparison with the shared total-lift and
multispan reconstruction theorems. The geometric interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3.2 (arXiv:1601.07081v4).
-/

public noncomputable section

open CategoryTheory Limits Set

universe u

namespace Mei.GradedCorrespondence

variable {R V H ι κ Λ : Type*} {U M B : Type u} [Semiring R]
  [AddCommMonoid U] [Module R U] [AddCommMonoid M] [Module R M]
  [DecidableEq κ] {𝒰 : ι → Submodule R U} {ℳ : κ → Submodule R M}
  [DirectSum.Decomposition ℳ] [AddCommMonoid B] [Module R B]
  {I : Set ι} {J : Set κ} (C : GradedCorrespondence (B := B) 𝒰 ℳ I J)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommMonoid H] [Module R H] (p : I) (α : H →ₗ[R] 𝒰 p)
  [AddCommGroup Λ] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (w₀ : Λ) (w : κ → Λ) (ν : V →L[ℝ] ℝ) (b : ℝ) (Z : Set V)
  (hν : Toric.IsRationalFunctional h ν.toLinearMap)
  (hZ : Z ⊆ {x | ν x = b}) (hsemi : IsRationalSemilinear h Z)

local notation "Sections" => SemimoduleCat.sectionsSubmodule
  (MultispanIndex.multispan (MultispanIndex.ofLinearMaps C.left C.right))
local notation "value" x:max Q:max =>
  FiniteSemilinearFamily.weightedEvaluation
    (C.singleFaceTransferFamily p (α x) h w₀ w ν b Z hν hZ hsemi)
    (fun q => (C.transfer p (Subtype.val q) (α x) : M)) Q

/-- The actual closed-family weighted values and the incoming coefficients
extend uniquely to matching sections, with one generic arrangement for the
whole finite-input test. The family may lose branches when the input varies. -/
theorem existsUnique_singleFaceTransferFamily_matchingFamily_of_fg
    (hinj : Function.Injective (C.left.prod C.right))
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ q x, C.transfer p q (α x) ≠ 0 → ν (i (w q)) = ν (i w₀))
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q → (ν Q - b) / ν (i w₀) < 0 →
      ∃! ℓ : H →ₗ[R] Sections, ∀ x,
        (ℓ x).val (.right false) = (α x : U) ∧ (ℓ x).val (.right true) = value x Q := by
  simpa only [singleFaceTransferFamily_weightedEvaluation] using
    C.existsUnique_singleFace_matchingFamily_of_fg p α (i w₀) (fun q => i (w q)) ν b Z
      hinj hα hnormal hZ A hcover hA

/-- The face value of the matching family is exactly the chosen total lift.
Conversely, this face value characterizes all the chamber evaluations of the
actual endpoint family at generic opposite-side endpoints. -/
theorem exists_singleFaceTransferFamily_matchingFamily_iff_of_fg
    (hinj : Function.Injective (C.left.prod C.right))
    (hα : (LinearMap.range α).FG)
    (hnormal : ∀ q x, C.transfer p q (α x) ≠ 0 → ν (i (w q)) = ν (i w₀))
    {δ : Type*} [Finite δ] (A : δ → AffineSubspace ℝ V)
    (hcover : Z ⊆ ⋃ j, (A j : Set V))
    (hA : ∀ j, ∃ x, ν x = b ∧ x ∉ A j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q → (ν Q - b) / ν (i w₀) < 0 →
      ∀ ℓ : H →ₗ[R] Sections,
        (∀ x, (ℓ x).val (.right false) = (α x : U) ∧
          (ℓ x).val (.right true) = value x Q) ↔
        ∀ x, (ℓ x).val (.left default) = C.liftLeft p (α x) := by
  obtain ⟨F, hF⟩ := C.exists_singleFaceTransferEvaluationLinear_eq_right_of_fg
    p (i w₀) (fun q => i (w q)) ν b Z α hα hnormal hZ A hcover hA
  refine ⟨F, fun Q hQ ht ℓ => ?_⟩
  have hv (x : H) : value x Q = C.right (C.liftLeft p (α x)) := by
    rw [singleFaceTransferFamily_weightedEvaluation,
      ← singleFaceTransferEvaluationLinear_apply_eq_evaluation C p (i w₀)
        (fun q => i (w q)) ν b Z α hZ, hF Q hQ ht]
    rfl
  constructor
  · intro hℓ x
    have hs := MultispanIndex.ofLinearMaps_apply_left C.left C.right default (ℓ x).property
    apply hinj
    exact Prod.ext (hs.1.trans ((hℓ x).1.trans (C.left_liftLeft_apply p (α x)).symm))
      (hs.2.trans ((hℓ x).2.trans (hv x)))
  · intro hℓ x
    have hs := MultispanIndex.ofLinearMaps_apply_left C.left C.right default (ℓ x).property
    rw [hℓ x] at hs
    exact ⟨hs.1.symm.trans (C.left_liftLeft_apply p (α x)), hs.2.symm.trans (hv x).symm⟩

end Mei.GradedCorrespondence
