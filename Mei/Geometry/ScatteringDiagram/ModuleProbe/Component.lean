/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Truncation
public import Mei.LinearAlgebra.GradedModule.Shifted.Component

/-!
# Homogeneous coefficient recovery from finite probes

Recovering the degree-`q` shifted coefficient of a truncated probe depends only
on its extended degree-`(q,1,0)` component. This connects homogeneous wall
logarithms with the ambient homogeneous components of shifted coefficients.
The comparison uses the existing quotient decomposition and the charge-one
projection of `ModuleProbe.grading`.
-/

public noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ L : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) (p : Γ) [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]

/-- Recovering a retained coefficient commutes with projection onto its
charge-one homogeneous piece. -/
@[simp]
theorem shiftedQuotientComponent_moduleQuotientProjection_decompose
    (q : Γ) (k : ℕ) (hk : d.degree (q - p) ≤ k)
    (x : (positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)) :
    d.shiftedQuotientComponent ℳ p q k hk
        (moduleQuotientProjection d ℳ p ℒ k
          (DirectSum.decompose ((positiveDegrees d p).truncatedGrading
            (grading d ℳ p ℒ) (k + 1)) x (q, 1, 0))) =
      d.shiftedQuotientComponent ℳ p q k hk
        (moduleQuotientProjection d ℳ p ℒ k x) := by
  obtain ⟨x, rfl⟩ := ((positiveDegrees d p).degreeIdeal
    (grading d ℳ p ℒ) (k + 1)).toSubmodule.mkQ_surjective x
  simp only [Submodule.mkQ_apply]
  simp only [PositiveDegrees.decompose_truncatedGrading_mk,
    moduleQuotientProjection_mk,
    PositiveDegrees.shiftedQuotientComponent_mk,
    coe_decompose_grading_module]
  simp only [moduleInclusion, LieAlgebra.SemiDirectSum.inl_eq_mk,
    LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_decompose_shiftedGrading]
  have hpq : p + (q - p) = q := by abel
  rw [hpq, DirectSum.decompose_of_mem_same _
    (DirectSum.decompose ℳ (moduleCoefficientsEquiv d ℳ p x.left : M) q).property]

end Mei.ModuleProbe
