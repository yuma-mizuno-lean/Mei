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

/-- Endpoint restriction of an inclusion family retains precisely the original
labels whose domains contain the endpoint and the restricting set. -/
def fiberOfDomainsRestrictEquiv {U : Set V} (hU : IsRationalSemilinear h U) (Q : V) :
    ((ofDomains D hD).restrict hU).fiber Q ≃ {t // Q ∈ D t ∧ Q ∈ U} :=
  ((ofDomains D hD).fiberRestrictEquiv hU Q).trans
    (((fiberOfDomainsEquiv D hD Q).subtypeEquiv (q := fun _ => Q ∈ U) fun z => by
      have hxQ : z.2.1.val = Q := (ofDomains_eval D hD _ _).symm.trans z.2.2
      simp only [hxQ]).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun t => Q ∈ D t) (fun _ : ι => Q ∈ U)))

@[simp]
theorem fiberOfDomainsRestrictEquiv_apply_val {U : Set V}
    (hU : IsRationalSemilinear h U) (Q : V)
    (z : ((ofDomains D hD).restrict hU).fiber Q) :
    (fiberOfDomainsRestrictEquiv hU Q z).val = z.1 := by
  calc
    (fiberOfDomainsRestrictEquiv hU Q z).val =
        (fiberOfDomainsEquiv D hD Q ((ofDomains D hD).fiberRestrictEquiv hU Q z).val).val :=
      rfl
    _ = ((ofDomains D hD).fiberRestrictEquiv hU Q z).val.1 :=
      fiberOfDomainsEquiv_apply_val ..
    _ = z.1 := fiberRestrictEquiv_apply_val_fst ..

@[simp]
theorem fiberOfDomainsRestrictEquiv_symm_apply_fst {U : Set V}
    (hU : IsRationalSemilinear h U) (Q : V) (z : {t // Q ∈ D t ∧ Q ∈ U}) :
    ((fiberOfDomainsRestrictEquiv (hD := hD) hU Q).symm z).1 = z.val := by
  have ht := fiberOfDomainsRestrictEquiv_apply_val (hD := hD) hU Q
    ((fiberOfDomainsRestrictEquiv (hD := hD) hU Q).symm z)
  simpa only [Equiv.apply_symm_apply] using ht.symm

instance {U : Set V} (hU : IsRationalSemilinear h U) (Q : V) :
    Finite (((ofDomains D hD).restrict hU).fiber Q) :=
  Finite.of_equiv _ (fiberOfDomainsRestrictEquiv hU Q).symm

open Classical in
/-- Endpoint restriction multiplies the original evaluation by the membership
indicator. The labels and their weights remain global. -/
theorem weightedEvaluation_ofDomains_restrict {U : Set V}
    (hU : IsRationalSemilinear h U) (weight : ι → M) (Q : V) :
    ((ofDomains D hD).restrict hU).weightedEvaluation weight Q =
      if Q ∈ U then (ofDomains D hD).weightedEvaluation weight Q else 0 := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite (((ofDomains D hD).restrict hU).fiber Q)
  rw [weightedEvaluation_def, weightedEvaluation_ofDomains]
  trans ∑ t : {t // Q ∈ D t ∧ Q ∈ U}, weight t.val
  · exact Fintype.sum_equiv (fiberOfDomainsRestrictEquiv hU Q) _ _ (fun _ => by simp)
  · trans ∑ t : ι, if Q ∈ D t ∧ Q ∈ U then weight t else 0
    · rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter fun t => Q ∈ D t ∧ Q ∈ U)
        (by simp) weight).symm
    · by_cases hQ : Q ∈ U <;> simp [hQ]

end Mei.FiniteSemilinearFamily
