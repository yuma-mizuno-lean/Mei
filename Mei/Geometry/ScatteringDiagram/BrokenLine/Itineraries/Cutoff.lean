/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Map

/-!
# Changing the cutoff of a decorated ray inventory

If a graded coefficient module is supported in a positive-degree cutoff, enlarging
the cutoff used to enumerate its rays adds no rays. Every segment decoration of a
contributing ray is nonzero, so its degree already belongs to the smaller cutoff.
The comparison retains all encounters, geometric paths and whole decorations.

Combined with `map_cutoffDecoratedEvaluation`, this gives coefficient comparisons
between different cutoffs, even when specialization kills some decorations. The
encounter alphabet and geometric admission conditions remain fixed.

We use `DecoratedAdmissibleRay.decoration_ne_zero` and `decoration_mem`, and
the actual all-itinerary family `CutoffDecoratedRay`. Whole-component propagation
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Definition 2.10 and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  {k l : ℕ} (h : k ≤ l)
  (hℳ : ∀ q (x : M), x ∈ ℳ q → x ≠ 0 → q ∈ d.cutoff k) (Q : V)

/-- A coefficient grading supported in cutoff `k` gives the same actual rays
when enumerated at any larger cutoff. No encounter is deleted or inserted. -/
def cutoffDecoratedRayCutoffEquiv :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q ≃
      CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q where
  toFun β :=
    { itinerary := β.itinerary
      realization := β.realization
      degree_mem := fun j => hℳ _ _ (β.realization.decoration_mem j)
        (β.realization.decoration_ne_zero j.castSucc)
      degree_sub_mem := β.degree_sub_mem }
  invFun β :=
    { itinerary := β.itinerary
      realization := β.realization
      degree_mem := fun j => d.cutoff_mono h (β.degree_mem j)
      degree_sub_mem := β.degree_sub_mem }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Changing the enumeration cutoff preserves the complete encounter word. -/
@[simp]
theorem cutoffDecoratedRayCutoffEquiv_itinerary
    (β : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q) :
    (cutoffDecoratedRayCutoffEquiv d ℳ T a v f c ε P W S C h hℳ Q β).itinerary =
      β.itinerary := (rfl)

/-- Changing the enumeration cutoff preserves the entire decorated realization,
including all segment degrees, incoming tails and encounter times. -/
@[simp]
theorem cutoffDecoratedRayCutoffEquiv_realization
    (β : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q) :
    HEq (cutoffDecoratedRayCutoffEquiv d ℳ T a v f c ε P W S C h hℳ Q β).realization
      β.realization := (HEq.rfl)

/-- The geometric ray is preserved without transporting its dependent encounter
index type. This includes the incoming affine tail. -/
@[simp]
theorem cutoffDecoratedRayCutoffEquiv_ray
    (β : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q) :
    (cutoffDecoratedRayCutoffEquiv d ℳ T a v f c ε P W S C h hℳ Q β).realization.2.ray =
      β.realization.2.ray := (rfl)

/-- The whole final decoration is unchanged by the cutoff comparison. -/
@[simp↓] -- Compare decorations before expanding their homogeneous-history formulas.
theorem cutoffDecoratedRayCutoffEquiv_decoration
    (β : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q) :
    (cutoffDecoratedRayCutoffEquiv d ℳ T a v f c ε P W S C h hℳ Q β).decoration =
      β.decoration := by
  simp only [CutoffDecoratedRay.decoration_eq, cutoffDecoratedRayCutoffEquiv,
    Equiv.coe_fn_mk]

include h hℳ in
/-- Enlarging the ray enumeration cutoff beyond the coefficient support does
not change the total weighted evaluation over all encounter itineraries. -/
theorem cutoffDecoratedEvaluation_eq_of_supported [Finite J] :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C l Q =
      cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q)
  let := Fintype.ofFinite (CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
  rw [cutoffDecoratedEvaluation_def, cutoffDecoratedEvaluation_def]
  exact Fintype.sum_equiv
    (cutoffDecoratedRayCutoffEquiv d ℳ T a v f c ε P W S C h hℳ Q) _ _
    (fun β => (cutoffDecoratedRayCutoffEquiv_decoration d ℳ T a v f c ε P W S C h hℳ Q β).symm)

end Mei
