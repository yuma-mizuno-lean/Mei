/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Realization
public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification
public import Mathlib.Topology.CompactOpen

/-!
# Closed degeneration charts for backward itineraries

The hinge formula for a backward itinerary defines a continuous family in the
compact-open topology on paths. At strictly positive elapsed times it is the
existing finite affine ray. The formula also makes sense at limits where times
vanish: encounters can coincide, while their positions and parameters retain
their affine formulas. No crossing is sent to infinity at a finite endpoint.

Every rational semilinear subdomain of a selected itinerary admits finitely many
disjoint charts that are relative interiors of closed rational-normal polyhedra.
On their closures the selected support incidences persist and elapsed times are
nonnegative. Each closed chart has a proper inclusion into endpoint space
because it is closed. Extra semilinear validity constraints may be imposed before
taking these charts; their boundary points need not satisfy strict avoidance
conditions.

Every extended path agrees eventually with its incoming affine line, regardless
of time order. A nonzero incoming direction therefore makes each half-line proper;
this compact-perturbation argument follows `FiniteAffineRay.isProperMap_restrict_Iic`.

The backward parameterization follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin (n + 1) → V)

/-- The hinge extension of the backward realization, continuous in the endpoint
for the compact-open topology on paths. Outside the weak time-order domain the
formula is totalized and need not have its given endpoint at time zero. -/
def backwardPath : C(V, C(ℝ, V)) :=
  ContinuousMap.curry ⟨fun z =>
    (∑ j : Fin n, max (backwardParameter f c (fun j => v j.castSucc) j.succ z.1 - z.2) 0 •
      (v j.succ - v j.castSucc)) - z.2 • v 0 + z.1, by
        apply Continuous.add
        · apply Continuous.sub
          · apply continuous_finsetSum
            intro j _
            exact (((backwardParameter f c (fun j => v j.castSucc) j.succ).continuous.comp
              continuous_fst).sub continuous_snd).max continuous_const |>.smul continuous_const
          · exact continuous_snd.smul continuous_const
        · exact continuous_fst⟩

/-- The extended family uses the same finite hinges even when encounter times coincide. -/
@[simp]
theorem backwardPath_apply (Q : V) (t : ℝ) :
    backwardPath f c v Q t =
      (∑ j : Fin n, max (backwardParameter f c (fun j => v j.castSucc) j.succ Q - t) 0 •
        (v j.succ - v j.castSucc)) - t • v 0 + Q := (rfl)

/-- On a strict itinerary the extended path is the actual finite affine ray,
including its affine continuation beyond time zero. -/
theorem backwardPath_eq_backwardRay (Q : V)
    (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q) :
    backwardPath f c v Q = (backwardRay f c v Q hpos).toContinuousMap := by
  classical
  ext t
  rw [FiniteAffineRay.toContinuousMap_apply, backwardPath_apply, FiniteAffineRay.eval_def,
    bends_backwardRay, direction_backwardRay, endpoint_backwardRay]
  rw [← Finsupp.sum_finsetSum_index (fun b => smul_zero (max (b - t) 0))
    (fun b x y => smul_add (max (b - t) 0) x y)]
  simp only [Finsupp.sum_single_index
    (h := fun b (x : V) => max (b - t) 0 • x) (smul_zero _), vadd_eq_add]

/-- Converging endpoints give compact-open convergence of the actual strict
realizations to the extended path, even when some limiting elapsed times vanish. -/
theorem tendsto_backwardRay {A : Type*} {l : Filter A} {Q : A → V} {Q₀ : V}
    (hQ : Tendsto Q l (𝓝 Q₀))
    (hpos : ∀ a j, 0 < backwardTime f c (fun j => v j.castSucc) j (Q a)) :
    Tendsto (fun a => (backwardRay f c v (Q a) (hpos a)).toContinuousMap) l
      (𝓝 (backwardPath f c v Q₀)) := by
  simpa only [← backwardPath_eq_backwardRay, Function.comp_def] using
    (backwardPath f c v).continuous.continuousAt.tendsto.comp hQ

private theorem backwardPath_partial_sum (Q : V) (j : Fin (n + 1)) (t : ℝ) :
    (∑ a ∈ Finset.univ.filter (fun a : Fin n => a.val < j.val),
      (backwardParameter f c (fun j => v j.castSucc) a.succ Q - t) •
        (v a.succ - v a.castSucc)) =
      backwardPoint f c (fun j => v j.castSucc) j Q +
        (backwardParameter f c (fun j => v j.castSucc) j Q - t) • v j +
          t • v 0 - Q := by
  classical
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    have he : Finset.univ.filter (fun a : Fin n => a.val < j.succ.val) =
        insert j (Finset.univ.filter (fun a : Fin n => a.val < j.castSucc.val)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [he, Finset.sum_insert (by simp), ih, backwardPoint_succ_apply,
      backwardParameter_succ]
    module

/-- With nonnegative elapsed times, the extended path passes through every affine
encounter point at its parameter. Several of those parameters may be equal. -/
theorem backwardPath_apply_parameter {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q)
    (j : Fin (n + 1)) :
    backwardPath f c v Q (backwardParameter f c (fun j => v j.castSucc) j Q) =
      backwardPoint f c (fun j => v j.castSucc) j Q := by
  classical
  have hanti := antitone_backwardParameter f c (fun j => v j.castSucc) Q hQ
  rw [backwardPath_apply]
  have he : (∑ a : Fin n,
      max (backwardParameter f c (fun j => v j.castSucc) a.succ Q -
        backwardParameter f c (fun j => v j.castSucc) j Q) 0 • (v a.succ - v a.castSucc)) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.val < j.val),
        (backwardParameter f c (fun j => v j.castSucc) a.succ Q -
          backwardParameter f c (fun j => v j.castSucc) j Q) • (v a.succ - v a.castSucc) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < j.val
    · rw [ite_eq_left ha, max_eq_left (sub_nonneg.mpr (hanti (by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ]; omega)))]
    · rw [ite_eq_right ha, max_eq_right (sub_nonpos.mpr (hanti (by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ]; omega))), zero_smul]
  rw [he, backwardPath_partial_sum]
  simp only [sub_self, zero_smul, add_zero]
  abel

/-- Nonnegative elapsed times suffice for the extended path to retain its endpoint. -/
theorem backwardPath_apply_zero {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q) :
    backwardPath f c v Q 0 = Q := by
  simpa only [backwardParameter_zero, backwardPoint_zero, ContinuousAffineMap.coe_id,
    id_eq] using
    backwardPath_apply_parameter f c v hQ 0

/-- With nonnegative elapsed times, the extended path retains the entire incoming
half-line from the last encounter, even when encounters coincide. -/
theorem backwardPath_apply_incoming {Q : V}
    (hQ : ∀ j, 0 ≤ backwardTime f c (fun j => v j.castSucc) j Q)
    {s : ℝ} (hs : 0 ≤ s) :
    backwardPath f c v Q (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s) =
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q + s • v (Fin.last n) := by
  have hanti := antitone_backwardParameter f c (fun j => v j.castSucc) Q hQ
  rw [backwardPath_apply]
  have hnonneg (j : Fin n) : 0 ≤ backwardParameter f c (fun j => v j.castSucc) j.succ Q -
      (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s) :=
    sub_nonneg.mpr ((sub_le_self _ hs).trans (hanti (Fin.le_last _)))
  simp_rw [max_eq_left (hnonneg _)]
  have he := backwardPath_partial_sum f c v Q (Fin.last n)
    (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s)
  simp only [Fin.val_last, Finset.filter_true_of_mem (fun (a : Fin n) _ => a.isLt)] at he
  rw [he]
  module

/-- For every endpoint, the extended path eventually agrees with its incoming
affine line at negative infinity, even without ordered encounter parameters. -/
theorem backwardPath_eventuallyEq_incoming (Q : V) :
    backwardPath f c v Q =ᶠ[atBot] fun t =>
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
        (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - t) •
          v (Fin.last n) := by
  have hle : ∀ᶠ t : ℝ in atBot, ∀ j : Fin n,
      t ≤ backwardParameter f c (fun j => v j.castSucc) j.succ Q :=
    eventually_all.mpr fun j => eventually_le_atBot _
  filter_upwards [hle] with t ht
  rw [backwardPath_apply]
  simp_rw [max_eq_left (sub_nonneg.mpr (ht _))]
  have he := backwardPath_partial_sum f c v Q (Fin.last n) t
  simp only [Fin.val_last, Finset.filter_true_of_mem (fun (a : Fin n) _ => a.isLt)] at he
  rw [he]
  module

/-- Eventual admission of the extended path is exactly eventual admission of its
incoming affine half-line, without a time-order hypothesis. -/
theorem backwardPath_eventually_mem_iff (C : Set V) {Q : V} :
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
  have he := backwardPath_eventuallyEq_incoming f c v Q
  constructor
  · intro h
    filter_upwards [htop.eventually h, htop.eventually he] with s hs heq
    -- Expand the local parameter abbreviation before cancelling the subtractions.
    simpa only [heq, b, sub_sub_cancel] using hs
  · intro h
    filter_upwards [hbot.eventually h, he] with t ht heq
    rwa [heq]

/-- A nonzero incoming direction makes every extended half-line proper, without
a time-order hypothesis. Stationary intermediate segments are allowed. -/
theorem isProperMap_backwardPath_restrict_Iic {Q : V}
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
  obtain ⟨d, hd⟩ := eventually_atBot.mp (backwardPath_eventuallyEq_incoming f c v Q)
  refine (l.isProperMap_restrict_Iic hlv b).of_eqOn_compl_isCompact
    (K := Subtype.val ⁻¹' Icc d b)
    ((backwardPath f c v Q).continuous.comp continuous_subtype_val)
    (isClosed_Iic.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc) ?_
  intro t ht
  have hle : t.val ≤ d := by
    have hn : ¬ d ≤ t.val := fun h => ht ⟨h, t.property⟩
    exact (lt_of_not_ge hn).le
  simp only [hl]
  exact hd t.val hle

variable (P : Fin n → Set V)

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- Any rational semilinear validity subdomain has finite closed degeneration
charts. Their relative interiors partition precisely that domain; their closures retain
nonnegative times and all selected closed-support incidences. Each chart inclusion
into endpoint space is proper because the chart is closed. -/
theorem exists_backwardClosedCharts {D : Set V}
    (hD : IsRationalSemilinear h D)
    (hvalid : D ⊆ backwardDomain f c (fun j => v j.castSucc) P)
    (hclosed : ∀ j, IsClosed (P j)) :
    ∃ (κ : Type) (_ : Finite κ) (K : κ → Set V),
      (∀ a, (K a).Nonempty ∧ IsRationalNormalPolyhedron h (K a) ∧
        K a ⊆ closure D ∧ K a ⊆ weakBackwardDomain f c (fun j => v j.castSucc) P ∧
          IsProperMap (fun Q : K a => (Q : V))) ∧
      (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (K a))
        (intrinsicInterior ℝ (K b))) ∧ ⋃ a, intrinsicInterior ℝ (K a) = D := by
  obtain ⟨κ, hκ, K, hK, hdisj, hcover⟩ := hD.exists_disjoint_intrinsicInteriors
  refine ⟨κ, hκ, K, ?_, hdisj, hcover⟩
  intro a
  have hweak : closure D ⊆ weakBackwardDomain f c (fun j => v j.castSucc) P :=
    closure_minimal
      (hvalid.trans (backwardDomain_subset_weakBackwardDomain f c _ P))
      (isClosed_weakBackwardDomain f c _ hclosed)
  exact ⟨(hK a).1, (hK a).2.1, (hK a).2.2, (hK a).2.2.trans hweak,
    (hK a).2.1.isClosed.isProperMap_subtypeVal⟩

end Mei.Convex
