/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Leading
public import Mei.Geometry.Convex.Sweep.Admissible.Straight
public import Mei.Geometry.Convex.Sweep.Admissible.WallEvent
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Generic leading coefficients of broken-line sums

For a finite family of polyhedral walls, the leading component of the full
decorated-ray sum is the incoming coefficient at generic endpoints. Encounters
use canonical signed simultaneous events: coincident walls are retained in a
single incidence set, while its two signs are distinct labels. Thus the leading
straight ray is counted once, even when its complete half-line crosses walls.
The generic-endpoint results use the whole affine space as incoming source;
the realization-level theorem retains arbitrary source admission. Stationary
and zero inputs are allowed.

The exceptional arrangement depends only on wall geometry and the incoming
direction. The same arrangement works for every cutoff and every incoming
coefficient when the propagation maps preserve the diagonal component. For
finite shifted BCH actions this condition follows from
`PositiveDegrees.decompose_truncatedBCHAction_same`.

We combine `exists_straightRayRealizationArrangement`,
`AdmissibleRayRealization.withWallEvents` and
`decompose_cutoffDecoratedEvaluation_zero`. This supplies the initial coefficient
in the last-change recursion of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}

section Semiring

variable {R M Γ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  {T : WallEvent ι → Module.End R M} {a : ℳ 0} {v : Γ → V} {k : ℕ} {Q : V} {C : Set V}

local notation "P" => fun e : WallEvent ι => WallEvent.support e W
local notation "ν" => fun e : WallEvent ι => WallEvent.normal e f
local notation "b" => fun e : WallEvent ι => WallEvent.offset e c
local notation "ε" => fun e : WallEvent ι => Prod.snd e
local notation "S" => fun _ : Unit => singularSupport W

/-- A complete straight incoming realization recovers the leading coefficient
after replacing its arbitrary wall representatives by canonical signed events.
All coincident indexed walls and every unchanged encounter are retained. -/
theorem decompose_cutoffDecoratedEvaluation_zero_of_wallEvents
    {n : ℕ} {u : Fin n → ι}
    (r : AdmissibleRayRealization (fun j => f (u j)) (fun j => c (u j))
      (fun _ => v 0) (fun j => W (u j)) W S C Q)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j)
    (hT : ∀ e x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T e x) 0 : M) = x) :
    (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v ν b ε P P S C k Q) 0 : M) = a := by
  have hregular (j : Fin n) : r.ray (r.parameter j.succ) ∉ singularSupport W := by
    apply r.avoids_singular ()
    simpa only [r.parameter_zero] using r.strictAnti_parameter.antitone (Fin.zero_le j.succ)
  have g := r.withWallEvents hker hregular hc
  have hs := r.normal_sign_wallEvents
  -- Package the finite tuple as a list using the canonical equivalence, so the
  -- dependent realization is transported together with its encounter alphabet.
  have hlead : ∀ z : Σ n, Fin n → WallEvent ι,
      AdmissibleRayRealization (fun j => (z.2 j).normal f)
        (fun j => (z.2 j).offset c) (fun _ => v 0)
        (fun j => (z.2 j).support W) P S C Q →
      (∀ j, SignType.sign ((z.2 j).normal f (v 0)) = (z.2 j).2) →
      (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v ν b ε P P S C k Q) 0 : M) = a := by
    intro z
    obtain ⟨word, rfl⟩ := List.equivSigmaTuple.surjective z
    intro g hε
    exact decompose_cutoffDecoratedEvaluation_zero word g hT hε
      (fun e => subset_iUnion P e)
      (fun _ _ e e' hx hx' he he' =>
        e.eq_of_mem_support_of_normal_sign_eq e' W f (v 0) hx hx' he he')
  exact hlead ⟨n, r.wallEvents⟩ g hs

/-- Geometry alone supplies an arrangement on whose complement the full
signed-event ray sum has the prescribed leading coefficient, simultaneously
for every cutoff and input. Propagation is required to preserve only the
degree-zero diagonal. There is no nonzero-velocity hypothesis. -/
theorem exists_leadingEvaluationArrangement [FiniteDimensional ℝ V]
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j) (v : Γ → V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∀ (T : WallEvent ι → Module.End R M),
        (∀ e x, x ∈ ℳ 0 → (DirectSum.decompose ℳ (T e x) 0 : M) = x) →
      ∀ (a : ℳ 0) (k : ℕ),
        (DirectSum.decompose ℳ
          (cutoffDecoratedEvaluation d ℳ T a v ν b ε P P S univ k Q) 0 : M) = a := by
  classical
  obtain ⟨A, hA⟩ := exists_straightRayRealizationArrangement f c
    hpoly hdim hker hc {v 0}
  refine ⟨A, fun Q hQ T hT a k => ?_⟩
  obtain ⟨n, u, r, _⟩ := hA Q hQ (v 0) (Finset.mem_singleton_self _)
  exact decompose_cutoffDecoratedEvaluation_zero_of_wallEvents r hker hc hT

end Semiring

namespace PositiveDegrees

variable {Γ : Type} {R L M : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ)

/-- The leading coefficient of actual finite shifted BCH ray sums is the
incoming coefficient off one geometric arrangement, at every cutoff. Signed
labels may be inverses or products of simultaneous wall labels. No consistency,
faithfulness, coefficient basis or nonzero spatial direction is required. -/
theorem exists_leadingEvaluationArrangement_shiftedBCHAction [FiniteDimensional ℝ V]
    (hpoly : ∀ j, TauCeti.IsConvexPolyhedron (W j))
    (hdim : ∀ j, Module.finrank ℝ (affineSpan ℝ (W j)).direction + 1 =
      Module.finrank ℝ V)
    (hker : ∀ j, (f j).toLinearMap.ker = (affineSpan ℝ (W j)).direction)
    (hc : ∀ j x, x ∈ W j → f j x = c j) (v : Γ → V) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q → ∀ (k : ℕ)
      (g : WallEvent ι → d.truncatedGroup ℒ k)
      (a : (d.shiftedQuotientGrading ℳ p k).piece 0),
      (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
        (cutoffDecoratedEvaluation d (d.shiftedQuotientGrading ℳ p k).piece
          (fun e => ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k (g e)).toLinearMap)
          a v (fun e => e.normal f) (fun e => e.offset c) (fun e => e.2)
          (fun e => e.support W) (fun e => e.support W)
          (fun _ : Unit => singularSupport W) univ k Q) 0 :
        (d.shiftedLieFiltration ℒ ℳ p).quotient k) = a := by
  classical
  -- Choose geometry before the cutoff: coefficient quotients vary with k,
  -- whereas the complete incoming straight realization does not.
  obtain ⟨A, hA⟩ := exists_straightRayRealizationArrangement f c
    hpoly hdim hker hc {v 0}
  refine ⟨A, fun Q hQ k g a => ?_⟩
  obtain ⟨n, u, r, _⟩ := hA Q hQ (v 0) (Finset.mem_singleton_self _)
  exact decompose_cutoffDecoratedEvaluation_zero_of_wallEvents r hker hc
    (fun e _ hx => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g e) hx)

end PositiveDegrees
end Mei
