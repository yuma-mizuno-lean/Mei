/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Leading.Generic

/-!
# The incoming component of simultaneous-event evaluations

The full weighted evaluation of canonical wall-event rays has the prescribed
incoming component away from one exceptional arrangement. The arrangement
uses only the active wall geometry and the incoming direction. It works for
all incoming coefficients and all coefficient cutoffs below the geometric
cutoff, including stationary and zero inputs. Coincident indexed walls and
unchanged-degree encounters are retained.

This is the source term in the backward-ray recurrence of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5). The straight-ray supplier is
`PositiveDegrees.exists_leadingEvaluationArrangement_shiftedBCHAction`;
its obstacle family is the original active walls, as in
`cutoffWallEventEvaluation`.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)

/-- One geometric arrangement recovers the relative-degree-zero source in the
actual simultaneous-event evaluation, uniformly in the input and the smaller
coefficient cutoff. No consistency or annihilating-action hypothesis is needed. -/
theorem exists_cutoffWallEventEvaluation_sourceArrangement (K : ℕ) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∀ (k : ℕ) (hkK : k ≤ K) (a : (d.shiftedQuotientGrading ℳ p k).piece 0),
        (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
          (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q) 0 :
            (d.shiftedLieFiltration ℒ ℳ p).quotient k) = a := by
  let := h.finiteDimensional
  obtain ⟨A, hA⟩ := d.exists_leadingEvaluationArrangement_shiftedBCHAction ℒ ℳ p
    (f := B.activeNormal K) (c := B.activeOffset K)
    (fun j => (B.wall j).isConvexPolyhedron)
    (fun j => (B.wall j).finrank_direction_add_one)
    (fun j => by
      rw [(B.wall j).direction_support]
      ext x
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        B.activeNormal_apply, h.continuousRealCharacter_apply])
    (fun j x hx => (B.wall j).offset_eq hx) (fun n => i (ρ (p + n)))
  refine ⟨A, fun Q hQ k hkK a => ?_⟩
  rw [cutoffWallEventEvaluation_def]
  simp only [wallEventPropagation_def]
  exact hA Q hQ k
    (fun e => (d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K e)) a

/-- Read the source identity in the ambient incoming degree, using the same
component maps as the endpoint recursion. The right side is the entire incoming
homogeneous coefficient, read in the ambient grading. -/
theorem exists_cutoffWallEventEvaluation_leadingComponentArrangement (K : ℕ) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∀ (k : ℕ) (hkK : k ≤ K) (a : (d.shiftedQuotientGrading ℳ p k).piece 0),
        d.shiftedQuotientComponent ℳ p p k (by simp)
          (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q) =
        d.shiftedQuotientComponent ℳ p p k (by simp) a := by
  obtain ⟨A, hA⟩ := exists_cutoffWallEventEvaluation_sourceArrangement d ℳ p ℒ H h B K
  refine ⟨A, fun Q hQ k hkK a => ?_⟩
  have he := congrArg (d.shiftedQuotientComponent ℳ p p k (by simp)) (hA Q hQ k hkK a)
  have hd := d.decompose_shiftedQuotientGrading ℳ p k (0 : d.monoid) (by simp)
    (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q)
  simp only [ZeroMemClass.coe_zero] at hd
  rw [hd] at he
  simp only [d.shiftedQuotientComponent_mk, coe_shiftedInclusion,
    ZeroMemClass.coe_zero] at he
  have hc := (d.shiftedQuotientComponent ℳ p (p + 0) k (by simp)
    (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q)).property
  have hp := DirectSum.decompose_of_mem_same ℳ (by simpa only [add_zero] using hc)
  apply Subtype.ext
  have he' := congrArg Subtype.val he
  rw [hp] at he'
  -- Normalize the ambient index on representatives, avoiding dependent casts
  -- between the pieces at p + 0 and p.
  have ht :
      (d.shiftedQuotientComponent ℳ p (p + 0) k (by simp)
        (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q) : M) =
      d.shiftedQuotientComponent ℳ p p k (by simp)
        (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q) := by
    obtain ⟨x, hx⟩ := ((d.shiftedFiltration ℳ p).submodule (k + 1)).mkQ_surjective
      (cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a univ Q)
    rw [← hx]
    simp only [Submodule.mkQ_apply, d.shiftedQuotientComponent_mk]
    exact congrArg (fun q => (DirectSum.decompose ℳ (x : M) q : M)) (add_zero p)
  exact ht.symm.trans he'

end Mei.ModuleProbe
