/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Changing the cutoff of a decorated ray inventory

If a graded coefficient module is supported in a positive-degree cutoff, enlarging
the cutoff used to enumerate its rays adds no rays. Every segment decoration of a
contributing ray is nonzero, so its degree already belongs to the smaller cutoff.
The comparison retains all encounters, geometric paths and whole decorations.

Combined with `map_cutoffDecoratedEvaluation`, this gives coefficient comparisons
between different cutoffs, even when specialization kills some decorations. The
encounter alphabet and geometric admission conditions remain fixed.

Without a support bound, the fiber of any fixed final degree is still independent
of the cutoff once that degree is retained. Hence each homogeneous component of
the weighted evaluation stabilizes at its intrinsic degree cutoff. This allows
lower-degree recursion with one common enumeration cutoff, following Mandel,
§3.3.3.

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

namespace CutoffDecoratedRay

variable {d ℳ T a v f c ε P W S C Q}

/-- Change the enumeration cutoff when every selected degree belongs to the
new cutoff, preserving the encounter word and decorated realization. -/
def ofCutoff (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q where
  itinerary := r.itinerary
  realization := r.realization
  degree_mem := h
  degree_sub_mem := r.degree_sub_mem

/-- Changing the cutoff retains the complete encounter word. -/
@[simp]
theorem ofCutoff_itinerary (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    (r.ofCutoff h).itinerary = r.itinerary := (rfl)

/-- Changing the cutoff retains the entire decorated realization. -/
@[simp]
theorem ofCutoff_realization (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    HEq (r.ofCutoff h).realization r.realization := (HEq.rfl)

/-- Changing the cutoff retains the geometric path without transporting indices. -/
@[simp]
theorem ofCutoff_ray (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    (r.ofCutoff h).realization.2.ray = r.realization.2.ray := (rfl)

/-- Changing the cutoff retains the final relative degree. -/
@[simp]
theorem ofCutoff_finalDegree (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    (r.ofCutoff h).finalDegree = r.finalDegree := by
  simp only [finalDegree_def, ofCutoff]

/-- Changing the cutoff retains the whole final decoration. -/
@[simp↓]
theorem ofCutoff_decoration (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (h : ∀ j, r.realization.1.val j ∈ d.cutoff l) :
    (r.ofCutoff h).decoration = r.decoration := by
  simp only [decoration_eq, ofCutoff]

end CutoffDecoratedRay

/-- A coefficient grading supported in cutoff `k` gives the same actual rays
when enumerated at any larger cutoff. No encounter is deleted or inserted. -/
def cutoffDecoratedRayCutoffEquiv :
    CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q ≃
      CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q where
  toFun β := β.ofCutoff fun j => hℳ _ _ (β.realization.decoration_mem j)
    (β.realization.decoration_ne_zero j.castSucc)
  invFun β := β.ofCutoff fun j => d.cutoff_mono h (β.degree_mem j)
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
  exact CutoffDecoratedRay.ofCutoff_decoration β _

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

section Components

variable {d ℳ T a v f c ε P W S C} {k l : ℕ} {Q : V}

/-- Rays with a fixed final degree have identical fibers at any two cutoffs
retaining that degree. Neither cutoff need dominate the other, and no support
bound on the graded coefficient module is required. -/
def cutoffDecoratedRayFinalDegreeEquiv (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l) :
    {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q} ≃
      {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q // r.finalDegree = q} where
  toFun r := ⟨r.val.ofCutoff (fun j => d.mem_cutoff.mpr
    ⟨(d.mem_cutoff.mp (r.val.degree_mem j)).1,
      (r.val.degree_le_finalDegree j).trans (r.property.symm ▸ hl)⟩), by
      simpa only [CutoffDecoratedRay.ofCutoff_finalDegree] using r.property⟩
  invFun r := ⟨r.val.ofCutoff (fun j => d.mem_cutoff.mpr
    ⟨(d.mem_cutoff.mp (r.val.degree_mem j)).1,
      (r.val.degree_le_finalDegree j).trans (r.property.symm ▸ hk)⟩), by
      simpa only [CutoffDecoratedRay.ofCutoff_finalDegree] using r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reversing the fixed-final-degree comparison swaps its cutoff bounds. -/
@[simp]
theorem cutoffDecoratedRayFinalDegreeEquiv_symm (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l) :
    (cutoffDecoratedRayFinalDegreeEquiv (ℳ := ℳ) (T := T) (a := a) (v := v)
      (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (C := C) (Q := Q)
      q hk hl).symm = cutoffDecoratedRayFinalDegreeEquiv q hl hk := (rfl)

/-- The cutoff comparison retains every encounter, including those that
preserve degree or spatial velocity. -/
@[simp]
theorem cutoffDecoratedRayFinalDegreeEquiv_itinerary (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l)
    (r : {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}) :
    (cutoffDecoratedRayFinalDegreeEquiv q hk hl r).val.itinerary = r.val.itinerary := (rfl)

/-- The cutoff comparison retains the whole decorated realization, including
the path, encounter times, incoming source and every segment decoration. -/
@[simp]
theorem cutoffDecoratedRayFinalDegreeEquiv_realization (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l)
    (r : {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}) :
    HEq (cutoffDecoratedRayFinalDegreeEquiv q hk hl r).val.realization r.val.realization :=
  (HEq.rfl)

/-- The entire geometric path, including its incoming half-line, is unchanged
without transporting the encounter index type. -/
@[simp]
theorem cutoffDecoratedRayFinalDegreeEquiv_ray (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l)
    (r : {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}) :
    (cutoffDecoratedRayFinalDegreeEquiv q hk hl r).val.realization.2.ray =
      r.val.realization.2.ray := (rfl)

/-- The fixed-final-degree comparison preserves the whole final coefficient. -/
@[simp↓] -- Compare coefficients before expanding their homogeneous-history formulas.
theorem cutoffDecoratedRayFinalDegreeEquiv_decoration (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l)
    (r : {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}) :
    (cutoffDecoratedRayFinalDegreeEquiv q hk hl r).val.decoration = r.val.decoration := by
  exact CutoffDecoratedRay.ofCutoff_decoration r.val _

/-- Once an output degree is retained, its component is independent of the
enumeration cutoff. The coefficient module, propagation, source and obstacles
are fixed, and may have unbounded degree support. -/
theorem decompose_cutoffDecoratedEvaluation_eq_of_degree_le [Finite J]
    (q : Γ) (hk : d.degree q ≤ k) (hl : d.degree q ≤ l) :
    DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q =
    DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C l Q) q := by
  classical
  apply Subtype.val_injective
  rw [decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree,
    decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree]
  let := Fintype.ofFinite
    {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}
  let := Fintype.ofFinite
    {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q // r.finalDegree = q}
  exact Fintype.sum_equiv (cutoffDecoratedRayFinalDegreeEquiv q hk hl) _ _
    (fun r => (cutoffDecoratedRayFinalDegreeEquiv_decoration q hk hl r).symm)

end Components

end Mei
