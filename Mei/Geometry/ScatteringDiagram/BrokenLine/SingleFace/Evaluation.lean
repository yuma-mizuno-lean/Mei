/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.SingleFace

/-!
# Weighted evaluation for a single face

Consider the only wall `{ν = b}`, with a singular set `Z` inside it. The incoming datum is a
homogeneous coefficient `a` of relative degree zero with incoming velocity `v 0`. It is
propagated through the face by finitely many signed wall maps `T j`, and the incoming tail
lies in the full open half-space `0 < (ν x - b) / ν (v 0)` bounded by the face.

A cutoff decorated ray meets the face at most once. At an endpoint on the source side it is
the unbent incoming ray (`ray_eq_straight_of_itinerary_eq_nil`), and it exists exactly when the
coefficient is nonzero. At an
endpoint on the other side the rays are indexed by the pairs `(j, η)` for which the
degree-`η` component of `T j a` is nonzero, has the normal velocity of the incoming degree
and the crossing sign of `j`, survives the enumeration cutoff, and crosses the face away
from `Z`. The crossing time is the same for every `η`, because the normal velocity is
preserved. Consequently the weighted evaluation is the incoming coefficient on the source
side, and the sum of the admitted components of the transfers on the other side. Components
which do not change the degree, or do not change the spatial velocity, are retained.

The evaluation specializes `Mei.cutoffDecoratedEvaluation` to one face. It combines
`Mei.DecoratedAdmissibleRay.encounter_count_le_one_singleFace` and
`Mei.Convex.AdmissibleRayRealization.nonempty_singleFace_one_iff` for the geometry with
`Mei.CutoffDecoratedRay.exists_of_word` to package fixed-itinerary rays. The interpretation of
these rays as broken lines through one wall follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei

variable {R M Γ V J : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup Γ] {d : PositiveDegrees Γ}
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V} {ε : J → SignType}
  (ν : V →L[ℝ] ℝ) (b : ℝ) {Z : Set V} {k : ℕ} {Q : V}

local notation "SingleFaceRay" => CutoffDecoratedRay d ℳ T a v (fun _ : J => ν) (fun _ : J => b) ε
  (fun _ : J => Set.ofPred fun x => ν x = b) (fun _ : Unit => Set.ofPred fun x => ν x = b)
  (fun _ : Unit => Z) (Set.ofPred fun x => 0 < (ν x - b) / ν (v 0)) k Q

variable {ν b}

namespace CutoffDecoratedRay

/-- A cutoff decorated ray through a single face records at most one encounter, even when
the encounter changes neither the degree nor the spatial velocity. -/
theorem itinerary_length_le_one_singleFace {I K : Type*} {P : J → Set V}
    {W : I → Set V} {S : K → Set V} {C : Set V}
    (r : CutoffDecoratedRay d ℳ T a v (fun _ => ν) (fun _ => b) ε P W S C k Q) :
    r.itinerary.length ≤ 1 :=
  r.realization.encounter_count_le_one_singleFace

/-- Without an encounter, the ray exists exactly when the coefficient is nonzero and the
endpoint lies in the source half-space. The singular set, which lies in the face, plays no
role. -/
theorem exists_itinerary_eq_nil_singleFace_iff (hZ : Z ⊆ {x | ν x = b}) :
    (∃ r : SingleFaceRay, r.itinerary = []) ↔
      (a : M) ≠ 0 ∧ 0 < (ν Q - b) / ν (v 0) := by
  constructor
  · rintro ⟨⟨l, β, hmem, hsub⟩, hl⟩
    dsimp only at hl
    subst hl
    refine ⟨?_, ?_⟩
    · simpa using β.decoration_ne_zero (Fin.last 0)
    · have hv : (fun j : Fin 1 => v (Fin.snoc (α := fun _ => Γ) β.1.val 0 j)) = fun _ => v 0 :=
        funext fun j => by
          rw [Subsingleton.elim j (Fin.last 0)]
          exact congrArg v (Fin.snoc_last _ _)
      exact (Convex.AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ).mp ⟨hv ▸ β.2⟩
  · rintro ⟨ha, hQ⟩
    have hdom := (Convex.nonempty_admissibleRayRealization_iff _ _ _ _ _ _ _ _).mp
      ((Convex.AdmissibleRayRealization.nonempty_singleFace_empty_iff hZ).mpr hQ)
    have hv : (fun j : Fin 1 => v (Fin.snoc (α := fun _ => Γ) (Fin.elim0 : Fin 0 → Γ) 0 j)) =
        fun _ => v 0 :=
      funext fun j => by
        rw [Subsingleton.elim j (Fin.last 0)]
        exact congrArg v (Fin.snoc_last _ _)
    rw [← hv] at hdom
    obtain ⟨r, hr, -⟩ := exists_of_word (d := d) (ℳ := ℳ) (T := T) (a := a) (v := v)
      (f := fun _ : J => ν) (c := fun _ : J => b) (ε := ε) (k := k) (Q := Q)
      (P := fun _ : J => {x | ν x = b}) (W := fun _ : Unit => {x | ν x = b})
      (S := fun _ : Unit => Z) (C := {x | 0 < (ν x - b) / ν (v 0)})
      (Fin.elim0 : Fin 0 → J)
      ⟨⟨Fin.elim0, by simpa using ha⟩, Convex.admissibleRayRealization _ _ _ _ _ _ _ _ hdom⟩
      (fun j => j.elim0) (fun i => i.elim0)
    exact ⟨r, by simpa using hr⟩

open Classical in
/-- The rays with one encounter are indexed by the pairs `(j, η)` for which the degree-`η`
component of `T j a` is nonzero, has the normal velocity of the incoming degree and the
crossing sign of `j`, survives the cutoff, and crosses the face on the far side of the
endpoint at a point outside `Z`. -/
theorem exists_degreeItinerary_eq_singleton_singleFace_iff (hZ : Z ⊆ {x | ν x = b})
    (j : J) (η : Γ) :
    (∃ r : SingleFaceRay, r.degreeItinerary = [(η, j)]) ↔
      η ∈ (DirectSum.decompose ℳ (T j a)).support ∧ η ∈ d.cutoff k ∧
        ν (v η) = ν (v 0) ∧ SignType.sign (ν (v 0)) = ε j ∧ (ν Q - b) / ν (v 0) < 0 ∧
        Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z := by
  constructor
  · rintro ⟨⟨l, ⟨p, β⟩, hmem, hsub⟩, hr⟩
    have hl : l.length = 1 := by simpa using congrArg List.length hr
    obtain ⟨j', rfl⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨rfl, rfl⟩ : p.1 0 = η ∧ j' = j := by simpa [degreeItinerary_eq] using hr
    obtain ⟨hne, hnorm⟩ := (mem_decoratedHistorySupport ℳ _ 0 a v _ _ p.1).mp p.2
    have hsnoc : Fin.snoc (α := fun _ => Γ) (p.1 : Fin [j'].length → Γ) 0 (Fin.succ 0) = 0 :=
      Fin.snoc_last _ _
    have hv : (fun i : Fin 2 => v (Fin.snoc (α := fun _ => Γ) (p.1 : Fin [j'].length → Γ) 0 i)) =
        ![v (p.1 0), v 0] := by
      funext i
      fin_cases i
      · exact congrArg v (Fin.snoc_castSucc (α := fun _ => Γ) _ _ 0)
      · exact congrArg v (Fin.snoc_last _ _)
    have hnormal : ν (v (p.1 0)) = ν (v 0) := by
      simpa only [hsnoc] using (hnorm 0).1
    have hsign : SignType.sign (ν (v 0)) = ε j' := by
      rw [← hnormal]
      exact (hnorm 0).2
    obtain ⟨ht, hx⟩ := (Convex.AdmissibleRayRealization.nonempty_singleFace_one_iff
      hnormal hZ).mp ⟨hv ▸ β⟩
    rw [hnormal] at ht hx
    refine ⟨?_, hmem 0, hnormal, hsign, ht, hx⟩
    rw [DFinsupp.mem_support_iff]
    intro h0
    apply hne
    rw [homogeneousHistory_succ_apply]
    simp [h0]
  · rintro ⟨hη, hcut, hnormal, hsign, ht, hx⟩
    have hdom := (Convex.nonempty_admissibleRayRealization_iff _ _ _ _ _ _ _ _).mp
      ((Convex.AdmissibleRayRealization.nonempty_singleFace_one_iff (Q := Q) hnormal hZ).mpr
        ⟨by rwa [hnormal], by rwa [hnormal]⟩)
    have hv : (fun i : Fin 2 =>
        v (Fin.snoc (α := fun _ => Γ) (fun _ : Fin 1 => η) 0 i)) = ![v η, v 0] := by
      funext i
      fin_cases i
      · exact congrArg v (Fin.snoc_castSucc (α := fun _ => Γ) _ _ 0)
      · exact congrArg v (Fin.snoc_last _ _)
    rw [← hv] at hdom
    have hsnoc : Fin.snoc (α := fun _ => Γ) (fun _ : Fin 1 => η) 0 (Fin.succ 0) = 0 :=
      Fin.snoc_last _ _
    have hhist : (fun _ : Fin 1 => η) ∈ decoratedHistorySupport ℳ (fun _ : Fin 1 => T j) 0 a v
        (fun _ => ν) (fun _ => ε j) := by
      rw [mem_decoratedHistorySupport]
      refine ⟨?_, fun i => ?_⟩
      · rw [homogeneousHistory_succ_apply]
        simpa using DFinsupp.mem_support_iff.mp hη
      · rw [Subsingleton.elim i 0, hsnoc]
        exact ⟨hnormal, by rw [hnormal]; exact hsign⟩
    obtain ⟨r, -, -, -, -, hdi, -⟩ := exists_of_word (d := d) (ℳ := ℳ) (T := T) (a := a) (v := v)
      (f := fun _ : J => ν) (c := fun _ : J => b) (ε := ε) (k := k) (Q := Q)
      (P := fun _ : J => {x | ν x = b}) (W := fun _ : Unit => {x | ν x = b})
      (S := fun _ : Unit => Z) (C := {x | 0 < (ν x - b) / ν (v 0)})
      (fun _ : Fin 1 => j)
      ⟨⟨fun _ => η, hhist⟩, Convex.admissibleRayRealization _ _ _ _ _ _ _ _ hdom⟩
      (fun _ => hcut) (fun i i' _ => by simp)
    exact ⟨r, by simpa using hdi⟩

end CutoffDecoratedRay

open Classical in
/-- Weighted evaluation through a single face. On the source side of the face it is the
incoming coefficient, and on the other side it is the sum, over the wall maps `T j` of the
matching crossing sign, of the components of `T j a` whose degree survives the cutoff, has the
normal velocity of the incoming degree, and crosses the face outside `Z`. A component of
unchanged degree is retained, and the zero coefficient contributes nothing. -/
theorem cutoffDecoratedEvaluation_singleFace [Fintype J] (hZ : Z ⊆ {x | ν x = b}) :
    cutoffDecoratedEvaluation d ℳ T a v (fun _ : J => ν) (fun _ : J => b) ε
      (fun _ : J => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
      {x | 0 < (ν x - b) / ν (v 0)} k Q =
      (if 0 < (ν Q - b) / ν (v 0) then (a : M) else 0) +
        if (ν Q - b) / ν (v 0) < 0 then
          ∑ j with SignType.sign (ν (v 0)) = ε j,
            ∑ η ∈ (DirectSum.decompose ℳ (T j a)).support with
              η ∈ d.cutoff k ∧ ν (v η) = ν (v 0) ∧ Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z,
              (DirectSum.decompose ℳ (T j a) η : M)
        else 0 := by
  let := Fintype.ofFinite (SingleFaceRay)
  have hnil : ∀ r : SingleFaceRay, r.itinerary = [] → r.degreeItinerary = [] := fun r hr =>
    List.length_eq_zero_iff.mp (by rw [CutoffDecoratedRay.length_degreeItinerary, hr]; rfl)
  rw [cutoffDecoratedEvaluation_def,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : SingleFaceRay => r.itinerary = [])]
  congr 1
  · by_cases h : (a : M) ≠ 0 ∧ 0 < (ν Q - b) / ν (v 0)
    · obtain ⟨r₀, hr₀⟩ := (CutoffDecoratedRay.exists_itinerary_eq_nil_singleFace_iff hZ).mpr h
      have hfil : Finset.univ.filter (fun r : SingleFaceRay => r.itinerary = []) = {r₀} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun hr => CutoffDecoratedRay.degreeItinerary_injective
          ((hnil r hr).trans (hnil r₀ hr₀).symm), fun hr => hr ▸ hr₀⟩
      rw [hfil, Finset.sum_singleton, r₀.decoration_eq_of_itinerary_eq_nil hr₀, ite_eq_left h.2]
    · have hfil : Finset.univ.filter (fun r : SingleFaceRay => r.itinerary = []) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun r _ hr => h ?_
        exact (CutoffDecoratedRay.exists_itinerary_eq_nil_singleFace_iff hZ).mp ⟨r, hr⟩
      rw [hfil, Finset.sum_empty]
      split_ifs with h2
      · exact (not_not.mp fun ha => h ⟨ha, h2⟩).symm
      · rfl
  · have hone : ∀ r : SingleFaceRay, r.itinerary ≠ [] →
        ∃ y : Σ _ : J, Γ, r.degreeItinerary = [(y.2, y.1)] := by
      intro r hr
      have h1 : r.degreeItinerary.length = 1 := by
        have := CutoffDecoratedRay.itinerary_length_le_one_singleFace r
        have := List.length_pos_iff.mpr hr
        rw [CutoffDecoratedRay.length_degreeItinerary]
        omega
      obtain ⟨⟨η, j⟩, h⟩ := List.length_eq_one_iff.mp h1
      exact ⟨⟨j, η⟩, h⟩
    choose y hy using hone
    by_cases hτ : (ν Q - b) / ν (v 0) < 0
    · rw [ite_eq_left hτ, Finset.sum_sigma'
        (Finset.univ.filter fun j => SignType.sign (ν (v 0)) = ε j)
        (fun j => (DirectSum.decompose ℳ (T j a)).support.filter fun η =>
          η ∈ d.cutoff k ∧ ν (v η) = ν (v 0) ∧ Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z)
        (fun j η => (DirectSum.decompose ℳ (T j a) η : M))]
      refine Finset.sum_bij (fun r hr => y r (Finset.mem_filter.mp hr).2) ?_ ?_ ?_ ?_
      · intro r hr
        obtain ⟨hη, hcut, hnormal, hsign, -, hx⟩ :=
          (CutoffDecoratedRay.exists_degreeItinerary_eq_singleton_singleFace_iff hZ
            (y r _).1 (y r _).2).mp ⟨r, hy r _⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsign⟩,
          Finset.mem_filter.mpr ⟨hη, hcut, hnormal, hx⟩⟩
      · intro r₁ hr₁ r₂ hr₂ h
        exact CutoffDecoratedRay.degreeItinerary_injective
          (by rw [hy r₁ (Finset.mem_filter.mp hr₁).2, hy r₂ (Finset.mem_filter.mp hr₂).2, h])
      · intro z hz
        obtain ⟨hsign, hη⟩ := Finset.mem_sigma.mp hz
        obtain ⟨hη, hcut, hnormal, hx⟩ := Finset.mem_filter.mp hη
        obtain ⟨r, hr⟩ := (CutoffDecoratedRay.exists_degreeItinerary_eq_singleton_singleFace_iff hZ
          z.1 z.2).mpr ⟨hη, hcut, hnormal, (Finset.mem_filter.mp hsign).2, hτ, hx⟩
        have hne : r.itinerary ≠ [] := fun h => by simp [hnil r h] at hr
        refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
        have := (hy r hne).symm.trans hr
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
        exact Sigma.ext this.2 (heq_of_eq this.1)
      · intro r hr
        exact r.decoration_eq_of_degreeItinerary_eq_singleton (hy r _)
    · rw [ite_eq_right hτ]
      refine Finset.sum_eq_zero fun r hr => ?_
      exact absurd (CutoffDecoratedRay.exists_degreeItinerary_eq_singleton_singleFace_iff hZ
        (y r _).1 (y r _).2 |>.mp ⟨r, hy r (Finset.mem_filter.mp hr).2⟩).2.2.2.2.1 hτ

/-- On the source side of the face the weighted evaluation is the incoming coefficient.
When `a ≠ 0`, the only ray is the unbent incoming ray. When `a = 0`, the ray family is empty
and the evaluation is zero. -/
@[simp]
theorem cutoffDecoratedEvaluation_singleFace_of_pos [Finite J] (hZ : Z ⊆ {x | ν x = b})
    (hQ : 0 < (ν Q - b) / ν (v 0)) :
    cutoffDecoratedEvaluation d ℳ T a v (fun _ : J => ν) (fun _ : J => b) ε
      (fun _ : J => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
      {x | 0 < (ν x - b) / ν (v 0)} k Q = (a : M) := by
  have := Fintype.ofFinite J
  rw [cutoffDecoratedEvaluation_singleFace hZ, ite_eq_left hQ, ite_eq_right hQ.asymm, add_zero]

/-- On the far side of the face the weighted evaluation is the sum of the transfers `T j a` of
the matching crossing sign, provided every nonzero component of each such transfer survives the
cutoff, has the normal velocity of the incoming degree, and crosses the face outside `Z`. -/
theorem cutoffDecoratedEvaluation_singleFace_of_neg [Fintype J] (hZ : Z ⊆ {x | ν x = b})
    (hQ : (ν Q - b) / ν (v 0) < 0)
    (hT : ∀ j, SignType.sign (ν (v 0)) = ε j → ∀ η,
      DirectSum.decompose ℳ (T j a) η ≠ 0 → η ∈ d.cutoff k ∧ ν (v η) = ν (v 0) ∧
        Q - ((ν Q - b) / ν (v 0)) • v η ∉ Z) :
    cutoffDecoratedEvaluation d ℳ T a v (fun _ : J => ν) (fun _ : J => b) ε
      (fun _ : J => {x | ν x = b}) (fun _ : Unit => {x | ν x = b}) (fun _ : Unit => Z)
      {x | 0 < (ν x - b) / ν (v 0)} k Q =
      ∑ j with SignType.sign (ν (v 0)) = ε j, (T j a : M) := by
  classical
  rw [cutoffDecoratedEvaluation_singleFace hZ, ite_eq_right hQ.not_gt, zero_add, ite_eq_left hQ]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.filter_true_of_mem fun η hη => hT j (Finset.mem_filter.mp hj).2 η
    (DFinsupp.mem_support_iff.mp hη)]
  exact DirectSum.sum_support_decompose ℳ (T j a)

end Mei
