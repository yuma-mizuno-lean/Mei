/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries

/-!
# Stabilization of decorated ray components

Every selected degree of a cutoff decorated ray has degree at most its final
degree. Consequently the fiber with a specified final degree is independent of
the enumeration cutoff once that degree is retained. The comparison preserves
the complete encounter word, decorated realization and whole final coefficient.
It does not change the coefficient module or the wall and singular sets.

The homogeneous component of the full weighted evaluation is the sum over this
final-degree fiber. It therefore stabilizes at the intrinsic degree cutoff,
even when the coefficient module has nonzero pieces in arbitrarily high degrees.
This allows a recursion through lower-degree incoming rays to use one common
enumeration cutoff throughout.

We use `PositiveDegrees.degree_le_of_add_eq`, the positive-shift conditions of
`CutoffDecoratedRay`, and Mathlib's homogeneous projections and finite-sum
reindexing. The degree recursion follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k l : ℕ} {Q : V}

namespace CutoffDecoratedRay

/-- The final degree survives the enumeration cutoff, including for a ray with
no encounters, whose final degree is zero. -/
theorem finalDegree_mem_cutoff
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q) :
    r.finalDegree ∈ d.cutoff k := by
  rw [finalDegree_def]
  exact Fin.lastCases (by simp) (fun j => by simpa using r.degree_mem j) 0

/-- Every selected segment degree is bounded by the final degree. Positivity
rules out an excursion to a higher degree followed by a return. -/
theorem degree_le_finalDegree
    (r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q)
    (j : Fin r.itinerary.length) :
    d.degree (r.realization.1.val j) ≤ d.degree r.finalDegree := by
  let z : Fin r.itinerary.length := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  have hz : r.finalDegree = r.realization.1.val z := by
    rw [finalDegree_def]
    exact Fin.snoc_castSucc _ _ z
  rw [hz]
  exact d.degree_le_of_add_eq (r.degree_sub_mem z j (by simp [z, Fin.le_def]))
    (add_sub_cancel _ _)

end CutoffDecoratedRay

/-- Rays with a fixed final degree have identical fibers at any two cutoffs
retaining that degree. Neither cutoff need dominate the other, and no support
bound on the graded coefficient module is required. -/
def cutoffDecoratedRayFinalDegreeEquiv (q : Γ)
    (hk : d.degree q ≤ k) (hl : d.degree q ≤ l) :
    {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q} ≃
      {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q // r.finalDegree = q} where
  toFun r := ⟨{
    itinerary := r.val.itinerary
    realization := r.val.realization
    degree_mem := fun j => d.mem_cutoff.mpr
      ⟨(d.mem_cutoff.mp (r.val.degree_mem j)).1,
        (r.val.degree_le_finalDegree j).trans (r.property.symm ▸ hl)⟩
    degree_sub_mem := r.val.degree_sub_mem }, by
      simpa only [CutoffDecoratedRay.finalDegree_def] using r.property⟩
  invFun r := ⟨{
    itinerary := r.val.itinerary
    realization := r.val.realization
    degree_mem := fun j => d.mem_cutoff.mpr
      ⟨(d.mem_cutoff.mp (r.val.degree_mem j)).1,
        (r.val.degree_le_finalDegree j).trans (r.property.symm ▸ hk)⟩
    degree_sub_mem := r.val.degree_sub_mem }, by
      simpa only [CutoffDecoratedRay.finalDegree_def] using r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

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
  simp only [CutoffDecoratedRay.decoration_eq, cutoffDecoratedRayFinalDegreeEquiv,
    Equiv.coe_fn_mk]

open Classical in
/-- A homogeneous component of the complete weighted evaluation sums exactly
the rays of that final degree. Distinct histories with equal or cancelling
weights remain separate summands. -/
theorem decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree [Finite J] (q : Γ) :
    (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
      let := Fintype.ofFinite
        {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}
      ∑ r : {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q},
        r.val.decoration := by
  classical
  let Rays := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
  let := Fintype.ofFinite Rays
  let := Fintype.ofFinite {r : Rays // r.finalDegree = q}
  have hcomponent (r : Rays) :
      (DirectSum.decompose ℳ r.decoration q : M) =
        if r.finalDegree = q then r.decoration else 0 := by
    split_ifs with hr
    · exact DirectSum.decompose_of_mem_same ℳ (hr ▸ r.decoration_mem)
    · exact DirectSum.decompose_of_mem_ne ℳ r.decoration_mem hr
  rw [cutoffDecoratedEvaluation_def, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  simp_rw [hcomponent]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- An output degree outside the enumeration cutoff contributes zero. This
also covers degrees outside the positive monoid. -/
@[simp]
theorem decompose_cutoffDecoratedEvaluation_eq_zero_of_notMem_cutoff [Finite J]
    {q : Γ} (hq : q ∉ d.cutoff k) :
    DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q = 0 := by
  apply Subtype.val_injective
  rw [decompose_cutoffDecoratedEvaluation_eq_sum_finalDegree]
  have : IsEmpty
      {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q} :=
    ⟨fun r => hq (r.property ▸ r.val.finalDegree_mem_cutoff)⟩
  simp

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

end Mei
