/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.SemilinearFamily.Domains
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Weighted evaluation of finite semilinear fibers

A chart can carry a fixed weight in an additive commutative monoid. When the
endpoint fiber is finite, its weighted evaluation sums those weights with their
chart multiplicities. For families of inclusion domains this is the sum of the
weights of domains containing the endpoint.

Restricting the endpoint domains retains the original chart weights. At an
endpoint in the restricting set the fiber and its weighted evaluation are
unchanged. This restricts endpoint parameters, without changing any global
history recorded by a chart label.
-/

public noncomputable section

open scoped BigOperators

namespace Mei.FiniteSemilinearFamily

variable {N V N' W ι M : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [AddCommGroup W] [Module ℝ W] {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  [Finite ι] [AddCommMonoid M] (F : Mei.FiniteSemilinearFamily h h' ι)

/-- The sum of the chart weights over the finite endpoint fiber, retaining
multiplicities of distinct chart points. -/
def weightedEvaluation (weight : ι → M) (Q : W) [Finite (F.fiber Q)] : M :=
  let := Fintype.ofFinite (F.fiber Q)
  ∑ z : F.fiber Q, weight z.1

/-- Weighted evaluation is the sum over the actual fiber, rather than its image
in the endpoint space. -/
theorem weightedEvaluation_def (weight : ι → M) (Q : W) [Finite (F.fiber Q)] :
    F.weightedEvaluation weight Q =
      let := Fintype.ofFinite (F.fiber Q)
      ∑ z : F.fiber Q, weight z.1 := (rfl)

@[simp]
theorem weightedEvaluation_zero (Q : W) [Finite (F.fiber Q)] :
    F.weightedEvaluation (fun _ => (0 : M)) Q = 0 := by
  simp [weightedEvaluation_def]

/-- Weighted evaluation is additive in the chart weights. -/
@[simp]
theorem weightedEvaluation_add (weight₁ weight₂ : ι → M) (Q : W) [Finite (F.fiber Q)] :
    F.weightedEvaluation (weight₁ + weight₂) Q =
      F.weightedEvaluation weight₁ Q + F.weightedEvaluation weight₂ Q := by
  simp [weightedEvaluation_def, Finset.sum_add_distrib]

/-- Weighted evaluation adds over a disjoint union of families. -/
@[simp]
theorem weightedEvaluation_sum {κ : Type*} [Finite κ]
    (G : Mei.FiniteSemilinearFamily h h' κ) (weightF : ι → M) (weightG : κ → M)
    (Q : W) [Finite (F.fiber Q)] [Finite (G.fiber Q)] :
    (F.sum G).weightedEvaluation (Sum.elim weightF weightG) Q =
      F.weightedEvaluation weightF Q + G.weightedEvaluation weightG Q := by
  let := Fintype.ofFinite (F.fiber Q)
  let := Fintype.ofFinite (G.fiber Q)
  let := Fintype.ofFinite ((F.sum G).fiber Q)
  rw [weightedEvaluation_def, weightedEvaluation_def, weightedEvaluation_def]
  trans ∑ z : F.fiber Q ⊕ G.fiber Q,
    Sum.elim (fun z => weightF z.1) (fun z => weightG z.1) z
  · apply (Fintype.sum_equiv (F.fiberSumEquiv G Q).symm _ _ ?_).symm
    intro z
    simp only [fiberSumEquiv_symm_apply_fst]
    cases z <;> rfl
  · exact Fintype.sum_sum_type _

open Classical in
/-- Restriction sums the original fiber weights only at parameter points in the
restricting set. Evaluation need not identify those points with the endpoint. -/
theorem weightedEvaluation_restrict {U : Set V} (hU : IsRationalSemilinear h U)
    (weight : ι → M) (Q : W) [Finite (F.fiber Q)] :
    (F.restrict hU).weightedEvaluation weight Q =
      let := Fintype.ofFinite (F.fiber Q)
      ∑ z : F.fiber Q, if (z.2.1 : V) ∈ U then weight z.1 else 0 := by
  let := Fintype.ofFinite (F.fiber Q)
  let := Fintype.ofFinite ((F.restrict hU).fiber Q)
  rw [weightedEvaluation_def]
  trans ∑ z : {z : F.fiber Q // (z.2.1 : V) ∈ U}, weight z.val.1
  · exact Fintype.sum_equiv (F.fiberRestrictEquiv hU Q) _ _ (fun _ => by simp)
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun z : F.fiber Q => (z.2.1 : V) ∈ U)
      (by simp) (fun z => weight z.1)).symm

variable (D : ι → Set V) (hD : ∀ t, IsRationalSemilinear h (D t))

open Classical in
/-- For inclusion charts each admitted label contributes once. -/
theorem weightedEvaluation_ofDomains (weight : ι → M) (Q : V) :
    (ofDomains D hD).weightedEvaluation weight Q =
      let := Fintype.ofFinite ι
      ∑ t : ι, if Q ∈ D t then weight t else 0 := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite ((ofDomains D hD).fiber Q)
  rw [weightedEvaluation_def]
  trans ∑ t : {t // Q ∈ D t}, weight t.val
  · exact Fintype.sum_equiv (fiberOfDomainsEquiv D hD Q) _ _ (fun _ => by simp)
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun t => Q ∈ D t) (by simp) weight).symm

variable {D hD}

open Classical in
/-- Endpoint restriction multiplies the original evaluation by the membership
indicator. The labels and their weights remain global. -/
theorem weightedEvaluation_ofDomains_restrict {U : Set V}
    (hU : IsRationalSemilinear h U) (weight : ι → M) (Q : V) :
    ((ofDomains D hD).restrict hU).weightedEvaluation weight Q =
      if Q ∈ U then (ofDomains D hD).weightedEvaluation weight Q else 0 := by
  let := Fintype.ofFinite ((ofDomains D hD).fiber Q)
  rw [weightedEvaluation_restrict]
  have hxQ (z : (ofDomains D hD).fiber Q) : (z.2.1 : V) = Q :=
    (ofDomains_eval D hD _ _).symm.trans z.2.2
  simp only [hxQ]
  by_cases hQ : Q ∈ U <;> simp [hQ, weightedEvaluation_def]

end Mei.FiniteSemilinearFamily
