/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange
import Mei.Data.Fin.LastChange

/-!
# Localizing the last degree change on a backward ray

For a cutoff decorated ray of nonzero final relative degree, locate its last
change of degree canonically. Its incoming degree is strictly smaller, its
whole output is the final decoration, and its position is the intersection of
the fixed backward ray from the endpoint with the selected wall hyperplane.
Thus the position depends only on the endpoint, final degree and wall, even
when the ray has later unchanged-degree encounters.

Regroup the full weighted evaluation, over all encounter itineraries, by these
last walls. This is the finite coefficient partition used before cutting the
incoming pieces in a backward-ray recursion. A change of degree with unchanged
spatial velocity is retained.

We use `Fin.existsUnique_first_change`,
`DecoratedAdmissibleRay.existsUnique_last_degree_change` and the straight-terminal
parameter formula. For the broken-line recursion see Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

namespace CutoffDecoratedRay

local notation "Rays" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q

private theorem nonconstant_degrees (r : Rays) (hq : r.finalDegree ≠ 0) :
    ¬ ∀ i, Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 i =
      Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 0 := by
  intro hc
  exact hq (by simpa only [Fin.snoc_last, ← finalDegree_def] using
    (hc (Fin.last r.itinerary.length)).symm)

/-- The encounter of the last degree change, indexed backwards from the endpoint.
A nonzero final relative degree ensures a change from the incoming degree zero. -/
def lastChangeIndex (r : Rays) (hq : r.finalDegree ≠ 0) : Fin r.itinerary.length :=
  (Fin.existsUnique_first_change
    (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0)
    (r.nonconstant_degrees hq)).choose

/-- The incoming degree differs from the final one, and all segments after the
canonical last change have the final degree. -/
theorem lastChangeIndex_spec (r : Rays) (hq : r.finalDegree ≠ 0) :
    let j := r.lastChangeIndex hq
    let b := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0
    b j.succ ≠ r.finalDegree ∧ ∀ i ≤ j.castSucc, b i = r.finalDegree := by
  simpa only [lastChangeIndex, finalDegree_def] using
    (Fin.existsUnique_first_change _ (r.nonconstant_degrees hq)).choose_spec.1

/-- The selected last change is independent of any alternate index satisfying
its characteristic degree conditions. -/
theorem lastChangeIndex_eq (r : Rays) (hq : r.finalDegree ≠ 0)
    (j : Fin r.itinerary.length)
    (hne : Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ ≠ r.finalDegree)
    (hp : ∀ i ≤ j.castSucc,
      Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 i = r.finalDegree) :
    r.lastChangeIndex hq = j := by
  exact ((Fin.existsUnique_first_change _ (r.nonconstant_degrees hq)).choose_spec.2
    j (by simpa only [← finalDegree_def] using And.intro hne hp)).symm

/-- The last changing encounter lies at a positive, explicitly determined time
on the backward ray of the final degree. Its incoming coefficient has strictly
smaller relative degree. No hypothesis on the propagation maps is required. -/
theorem lastChangeIndex_localization (r : Rays) (hq : r.finalDegree ≠ 0) :
    let j := r.lastChangeIndex hq
    let w := r.itinerary.get j
    let b := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0
    let τ := (c w - f w Q) / f w (v r.finalDegree)
    f w (v r.finalDegree) ≠ 0 ∧ 0 < τ ∧
      r.realization.2.parameter j.succ = -τ ∧
      r.realization.2.ray (r.realization.2.parameter j.succ) =
        Q + τ • v r.finalDegree ∧
      Q + τ • v r.finalDegree ∈ P w ∧
      SignType.sign (f w (v r.finalDegree)) = ε w ∧
      d.degree (b j.succ) < d.degree r.finalDegree := by
  dsimp only
  let j := r.lastChangeIndex hq
  let b := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0
  obtain ⟨hne, hp⟩ := r.lastChangeIndex_spec hq
  have hj : r.realization.1.val j = r.finalDegree := by
    simpa only [Fin.snoc_castSucc] using hp j.castSucc le_rfl
  -- The terminal directions fix the encounter parameter and position.
  have ht : r.realization.2.parameter j.succ < 0 := by
    simpa only [r.realization.2.parameter_zero] using
      r.realization.2.strictAnti_parameter (Fin.succ_pos j)
  have hv := r.realization.2.parameter_eq_div_of_directions_eq j
    (fun i hi => congrArg v ((hp i hi).trans (r.finalDegree_def)))
  have htime : r.realization.2.parameter j.succ =
      -((c (r.itinerary.get j) - f (r.itinerary.get j) Q) /
        f (r.itinerary.get j) (v r.finalDegree)) := by
    simpa only [← finalDegree_def, ← neg_div, neg_sub] using hv
  have hpoint := r.realization.2.ray_eq_endpoint_sub_smul j.succ
    (fun i hi => congrArg v ((hp i (Fin.le_castSucc_iff.mpr hi)).trans r.finalDegree_def))
    ⟨le_rfl, ht.le⟩
  rw [← finalDegree_def, htime, neg_smul, sub_neg_eq_add] at hpoint
  rw [← htime] at hpoint
  -- Extend monotonicity to the incoming zero degree when this is the first encounter.
  have hstep : r.finalDegree - b j.succ ∈ d.monoid := by
    by_cases hlast : j.succ = Fin.last r.itinerary.length
    · have hi := r.degree_mem j
      simpa only [b, hlast, Fin.snoc_last, sub_zero, hj] using (d.mem_cutoff.mp hi).1
    · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hlast
      have hs := r.degree_sub_mem j i (by
        have he := congrArg Fin.val hi
        simp only [Fin.val_castSucc, Fin.val_succ] at he
        omega)
      simpa only [b, ← hi, Fin.snoc_castSucc, hj] using hs
  have hdeg := d.degree_pos hstep (sub_ne_zero.mpr hne.symm)
  refine ⟨?_, ?_, htime, hpoint, ?_, ?_, ?_⟩
  · simpa only [Fin.snoc_castSucc, hj] using r.realization.2.transverse j
  · linarith [htime]
  · exact hpoint ▸ r.realization.2.incidence j
  · simpa only [hj] using r.realization.crossing_sign j
  · simpa only [map_sub, sub_pos] using hdeg

end CutoffDecoratedRay

open Classical in
/-- For a nonzero final relative degree, group the full cutoff evaluation by the
wall of its last change. Each summand is the selected whole component of the
actual incoming decoration, at the position and smaller degree described by
`CutoffDecoratedRay.lastChangeIndex_localization`. The sum retains every
encounter itinerary and imposes no genericity or coefficient basis hypothesis. -/
theorem decompose_cutoffDecoratedEvaluation_eq_sum_lastChange [Finite J]
    (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x)
    (q : Γ) (hq : q ≠ 0) :
    let F := {r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q // r.finalDegree = q}
    let index := fun r : F => r.val.lastChangeIndex (r.property.symm ▸ hq)
    let := Fintype.ofFinite F
    let := Fintype.ofFinite J
    (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
      ∑ w : J, ∑ r : F,
        if r.val.itinerary.get (index r) = w then
          (DirectSum.decompose ℳ
            (T w (r.val.realization.decoration (index r).succ)) q : M)
        else 0 := by
  classical
  dsimp only
  let Rays := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
  let F := {r : Rays // r.finalDegree = q}
  let := Fintype.ofFinite Rays
  let := Fintype.ofFinite F
  let := Fintype.ofFinite J
  let index (r : F) := r.val.lastChangeIndex (r.property.symm ▸ hq)
  -- Later diagonal encounters preserve the whole last-change output.
  have hweight (r : F) : r.val.decoration =
      (DirectSum.decompose ℳ (T (r.val.itinerary.get (index r))
        (r.val.realization.decoration (index r).succ)) q : M) := by
    obtain ⟨j, ⟨hne, hp, hw, _⟩, _⟩ :=
      r.val.realization.existsUnique_last_degree_change
        (fun j => hT (r.val.itinerary.get j))
        (r.val.nonconstant_degrees (r.property.symm ▸ hq))
    have hj := r.val.lastChangeIndex_eq (r.property.symm ▸ hq) j
      (by simpa only [r.val.finalDegree_def] using hne)
      (by simpa only [r.val.finalDegree_def] using hp)
    rw [← hj] at hw
    rw [CutoffDecoratedRay.decoration_eq, ← DecoratedAdmissibleRay.decoration_zero]
    exact hw.trans (congrArg (fun s =>
      (DirectSum.decompose ℳ (T (r.val.itinerary.get (index r))
        (r.val.realization.decoration (index r).succ)) s : M))
      (r.val.finalDegree_def.symm.trans r.property))
  have hcomponent (r : Rays) :
      (DirectSum.decompose ℳ r.decoration q : M) =
        if r.finalDegree = q then r.decoration else 0 := by
    split_ifs with hr
    · exact DirectSum.decompose_of_mem_same ℳ (hr ▸ r.decoration_mem)
    · exact DirectSum.decompose_of_mem_ne ℳ r.decoration_mem hr
  calc
    _ = ∑ r : Rays, if r.finalDegree = q then r.decoration else 0 := by
      rw [cutoffDecoratedEvaluation_def, DirectSum.decompose_sum,
        DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl (fun r _ => hcomponent r)
    _ = ∑ r : F, r.val.decoration := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ w : J, ∑ r : F,
        if r.val.itinerary.get (index r) = w then r.val.decoration else 0 := by
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro r _
      split_ifs with hr
      · simpa only [hr] using hweight r
      · rfl

end Mei
