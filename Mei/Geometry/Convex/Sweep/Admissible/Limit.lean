/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Sweep.Degeneration

/-!
# Limits of admissible incoming rays

The compact-open closure of an admissible backward family consists exactly of
the extended paths at endpoints in the closure of its full admissible domain.
These paths retain their endpoints, all selected closed-support incidences and
nonnegative elapsed times. Their incoming tails remain admitted by a
rational-normal polyhedral source. In particular, taking a limit does not lose
the incoming source even though its admission threshold can depend on the path.

The path family over the closed endpoint domain is proper. Each individual
limiting half-line is also proper when its incoming direction is nonzero,
even if several encounters collapse. Boundary paths need not avoid the walls
or singular sets, and are not asserted to be transverse realizations.

We use `backwardPath`, the local characterization of
`AdmissibleRayRealization`, `backwardRay_eventually_mem_iff`, and
`IsRationalNormalPolyhedron.eventually_add_smul_mem`. The properness argument
follows `FiniteAffineRay.isProperMap_restrict_Iic` by comparison with the
incoming affine line. The backward parameterization is that of
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter Topology

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V)

/-- With weak time order, eventual admission of the extended path is exactly
eventual admission of its incoming affine half-line. -/
theorem backwardPath_eventually_mem_iff {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    (∀ᶠ t : ℝ in atBot, backwardPath f c v Q t ∈ C) ↔
      ∀ᶠ s : ℝ in atTop,
        backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
          s • v (Fin.last n) ∈ C := by
  let b := backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q
  have htop : Tendsto (fun s : ℝ => b - s) atTop atBot := by
    simpa only [sub_eq_add_neg] using
      tendsto_atBot_add_const_left atTop b tendsto_neg_atTop_atBot
  have hbot : Tendsto (fun t : ℝ => b - t) atBot atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_left atBot b tendsto_neg_atBot_atTop
  constructor
  · intro h
    filter_upwards [htop.eventually h, eventually_ge_atTop (0 : ℝ)] with s hs hnonneg
    rwa [backwardPath_apply_incoming f c v hQ hnonneg] at hs
  · intro h
    filter_upwards [hbot.eventually h, eventually_le_atBot b] with t ht hle
    have he := backwardPath_apply_incoming f c v hQ (sub_nonneg.mpr hle)
    -- Expand the local abbreviation so the two subtractions can cancel.
    dsimp only [b] at he
    rw [sub_sub_cancel] at he
    rwa [he]

/-- A nonzero incoming direction makes each limiting half-line proper.
Collapsed encounters and stationary intermediate segments are allowed. -/
theorem isProperMap_backwardPath_restrict_Iic {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q)
    (hv : v (Fin.last n) ≠ 0) (b : ℝ) :
    IsProperMap (fun t : Iic b => backwardPath f c v Q t) := by
  let a := backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q
  let X := backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q
  let l : ℝ →ᴬ[ℝ] V := ContinuousAffineMap.lineMap (X + a • v (Fin.last n))
    (X + a • v (Fin.last n) - v (Fin.last n))
  have hl (t : ℝ) : l t = X + (a - t) • v (Fin.last n) := by
    simp only [l, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply,
      vadd_eq_add, vsub_eq_sub]
    module
  have hlv : l.contLinear 1 ≠ 0 := by
    simpa only [l, ContinuousAffineMap.coe_contLinear,
      ContinuousAffineMap.lineMap_toAffineMap, AffineMap.lineMap_linear,
      LinearMap.smulRight_apply, LinearMap.id_apply, one_smul,
      vsub_eq_sub, sub_sub_cancel_left, neg_ne_zero] using hv
  refine (l.isProperMap_restrict_Iic hlv b).of_eqOn_compl_isCompact
    (K := Subtype.val ⁻¹' Icc a b)
    ((backwardPath f c v Q).continuous.comp continuous_subtype_val)
    (isClosed_Iic.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc) ?_
  intro t ht
  have hle : t.val ≤ a := by
    have hn : ¬ a ≤ t.val := fun h => ht ⟨h, t.property⟩
    exact (lt_of_not_ge hn).le
  simp only [hl]
  simpa only [a, X, sub_sub_cancel] using
    backwardPath_apply_incoming f c v hQ (sub_nonneg.mpr hle)

/-- Closing the full admissible domain retains all selected closed supports
and weakens strict time order to nonnegative elapsed times. -/
theorem closure_admissibleBackwardDomain_subset_weakBackwardDomain
    (hP : ∀ j, IsClosed (P j)) :
    closure (admissibleBackwardDomain f c v P W S C) ⊆
      weakBackwardDomain f c (fun j => v j.castSucc) P :=
  closure_minimal
    ((admissibleBackwardDomain_subset_backwardDomain f c v P W S C).trans
      (backwardDomain_subset_weakBackwardDomain f c _ P))
    (isClosed_weakBackwardDomain f c _ hP)

/-- Every limiting elapsed time is nonnegative, even if the selected supports
are not closed. -/
theorem backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain
    {Q : V} (hQ : Q ∈ closure (admissibleBackwardDomain f c v P W S C)) (j : Fin n) :
    0 ≤ backwardTime f c (fun j => v j.castSucc) j Q := by
  apply closure_minimal (s := admissibleBackwardDomain f c v P W S C)
    (t := (backwardTime f c (fun j => v j.castSucc) j) ⁻¹' Ici 0) _
    (isClosed_Ici.preimage (backwardTime f c (fun j => v j.castSucc) j).continuous) hQ
  intro Q hQ
  exact ((mem_backwardDomain _ _ _ _ _).mp
    (admissibleBackwardDomain_subset_backwardDomain f c v P W S C hQ) j).1.le

/-- The extended path at an admitted endpoint is the actual admissible ray. -/
@[simp]
theorem AdmissibleRayRealization.toContinuousMap_eq_backwardPath {Q : V}
    (r : AdmissibleRayRealization f c v P W S C Q) :
    r.ray.toContinuousMap = backwardPath f c v Q := by
  obtain ⟨hpos, _, hr⟩ := r.eq_backwardRay
  rw [hr, backwardPath_eq_backwardRay f c v Q hpos]

/-- Endpoint limits give compact-open limits of actual admissible rays.
The limiting endpoint need not itself be admissible. -/
theorem tendsto_admissibleRayRealization {A : Type*} {l : Filter A}
    {Q : A → V} {Q₀ : V} (hQ : Tendsto Q l (𝓝 Q₀))
    (r : ∀ a, AdmissibleRayRealization f c v P W S C (Q a)) :
    Tendsto (fun a => (r a).ray.toContinuousMap) l
      (𝓝 (backwardPath f c v Q₀)) := by
  simpa only [AdmissibleRayRealization.toContinuousMap_eq_backwardPath,
    Function.comp_def] using
    (backwardPath f c v).continuous.continuousAt.tendsto.comp hQ

/-- The path family on the closed admissible endpoint domain is proper:
evaluation at time zero recovers its endpoint. This is properness of the
family in compact-open path space, without a nonzero-direction hypothesis. -/
theorem isProperMap_backwardPath_closure_admissibleBackwardDomain :
    IsProperMap (fun Q : closure (admissibleBackwardDomain f c v P W S C) =>
      backwardPath f c v Q.val) := by
  have he : (fun Q : closure (admissibleBackwardDomain f c v P W S C) =>
      backwardPath f c v Q.val 0) = Subtype.val := by
    funext Q
    exact backwardPath_apply_zero f c v
      (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C Q.property)
  apply isProperMap_of_comp_of_t2
    ((backwardPath f c v).continuous.comp continuous_subtype_val)
    (continuous_eval_const (0 : ℝ))
  -- Expose evaluation after composition to apply the endpoint identity `he`.
  change IsProperMap (fun Q : closure (admissibleBackwardDomain f c v P W S C) =>
    backwardPath f c v Q.val 0)
  rw [he]
  exact isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap

/-- Every compact-open limiting path, and only such a path, is obtained by
extending backward propagation to the closure of the full admissible domain.
In particular there are no additional limits from escaping endpoints. -/
theorem closure_image_backwardPath_admissibleBackwardDomain :
    closure (backwardPath f c v '' admissibleBackwardDomain f c v P W S C) =
      backwardPath f c v '' closure (admissibleBackwardDomain f c v P W S C) := by
  apply le_antisymm
  · apply closure_minimal (image_mono subset_closure)
    have hc := (isProperMap_backwardPath_closure_admissibleBackwardDomain
      f c v P W S C).isClosedMap.isClosed_range
    -- Present the restricted path family as a composition with the subtype inclusion.
    change IsClosed (range ((backwardPath f c v) ∘
      (Subtype.val : closure (admissibleBackwardDomain f c v P W S C) → V))) at hc
    simpa only [range_comp, Subtype.range_coe_subtype, ofPred_mem_eq] using hc
  · exact image_closure_subset_closure_image (backwardPath f c v).continuous

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- The incoming source persists at every boundary endpoint of the full
admissible family. Polyhedrality controls eventual admission uniformly through
the closed domain of incoming base points, without a uniform entry time. -/
theorem backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain
    (hC : IsRationalNormalPolyhedron h C)
    {Q : V} (hQ : Q ∈ closure (admissibleBackwardDomain f c v P W S C)) :
    ∀ᶠ t : ℝ in atBot, backwardPath f c v Q t ∈ C := by
  apply (backwardPath_eventually_mem_iff f c v C
    (backwardTime_nonneg_of_mem_closure_admissibleBackwardDomain f c v P W S C hQ)).mpr
  have hc : IsClosed {Q : V | ∀ᶠ s : ℝ in atTop,
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
        s • v (Fin.last n) ∈ C} :=
    (hC.eventually_add_smul_mem (v (Fin.last n))).isClosed.preimage
      (backwardPoint f c (fun j => v j.castSucc) (Fin.last n)).continuous
  apply closure_minimal (s := admissibleBackwardDomain f c v P W S C) _ hc hQ
  intro Q hQ
  exact (mem_backwardIncomingDomain _ _ _ _ _ _ _ _).mp
    ((mem_admissibleBackwardDomain f c v P W S C Q).mp hQ).2.1 |>.2.2

end Mei.Convex
