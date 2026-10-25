/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.Algebra.DirectSum.Degree.Map
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Positive gradings on submodules and quotients

Positive support passes to images of homogeneous pieces and to inverse images under
injective maps. In particular, the inherited decompositions of homogeneous submodules
and quotients are positive. Their degree filtrations are respectively the restriction
and the image of the original filtration.

The quotient instance uses `TauCeti.InternalGrading.quotient`; the filtration comparison
uses Tau Ceti's `DirectSum.map_decompose_shift` to commute an injective graded map with
homogeneous projections. No finite generation or freeness is required.
-/

public section

namespace Mei

variable {N R M M' : Type*} [AddCommMonoid N] [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (d : PositiveDegrees N)

namespace IsPositiveGrading

variable (ℒ : N → Submodule R M) [IsPositiveGrading d ℒ]

/-- Images of positive homogeneous pieces still have positive support. -/
instance map (f : M →ₗ[R] M') :
    IsPositiveGrading d (fun n => (ℒ n).map f) where
  eq_bot n hn := by rw [eq_bot (d := d) (ℒ := ℒ) n hn, Submodule.map_bot]

/-- An injective linear map pulls positive support back to its source. -/
theorem comap (f : M' →ₗ[R] M) (hf : Function.Injective f) :
    IsPositiveGrading d (fun n => (ℒ n).comap f) where
  eq_bot n hn := by
    rw [eq_bot (d := d) (ℒ := ℒ) n hn, Submodule.comap_bot,
      LinearMap.ker_eq_bot_of_injective hf]

end IsPositiveGrading

namespace PositiveDegrees

/-- Taking images of all pieces commutes with the degree filtration. -/
@[simp]
theorem degreeSubmodule_map (ℒ : N → Submodule R M) (f : M →ₗ[R] M') (k : ℕ) :
    d.degreeSubmodule (fun n => (ℒ n).map f) k = (d.degreeSubmodule ℒ k).map f := by
  simp only [degreeSubmodule_def, Submodule.map_iSup]

/-- An injective degree-preserving map pulls back the ambient degree filtration. -/
theorem degreeSubmodule_comap [DecidableEq N]
    (ℒ : N → Submodule R M) [DirectSum.Decomposition ℒ]
    (ℳ : N → Submodule R M') [DirectSum.Decomposition ℳ]
    (f : M' →ₗ[R] M) (hf : Function.Injective f)
    (hmap : ∀ n x, x ∈ ℳ n → f x ∈ ℒ n) (k : ℕ) :
    d.degreeSubmodule ℳ k = (d.degreeSubmodule ℒ k).comap f := by
  rw [degreeSubmodule_eq_degreeTail, degreeSubmodule_eq_degreeTail]
  exact (f.comap_degreeTail_eq_of_injective ℳ ℒ hf hmap d.degree (k + 1)).symm

end PositiveDegrees

section Quotient

variable {ι : Type} [AddCommMonoid ι] (e : PositiveDegrees ι)
  {A V : Type*} [Ring A] [AddCommGroup V] [Module A V] [DecidableEq ι]
  (G : TauCeti.InternalGrading A V ι) (U : Submodule A V)
  (hU : DirectSum.SetLike.IsHomogeneous G.piece U)

/-- The inherited grading of a homogeneous quotient is positive. -/
instance IsPositiveGrading.quotient [IsPositiveGrading e G.piece] :
    IsPositiveGrading e (G.quotient U hU).piece := by
  rw [funext (G.quotient_piece U hU)]
  infer_instance

end Quotient
end Mei
