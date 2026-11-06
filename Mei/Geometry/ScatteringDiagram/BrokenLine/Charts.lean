/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.BigOperators.Group.Finset.Indicator
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Family

/-!
# Polyhedral charts for decorated rays

The full family of cutoff decorated rays is a finite disjoint union of endpoint
charts. Each chart is the relative interior of a nonempty closed rational-normal
polyhedron and carries one fixed decorated type. Its endpoint map is the inclusion
in the ambient space. The parameterization retains the actual rays, their incoming
tails and their whole decorations, without a genericity assumption. Charts belonging
to different types can have coincident images; those contributions remain distinct.

The closed polyhedra add only limits of valid endpoints. This statement does not
assert that boundary endpoints themselves admit transverse rays. Weighted evaluation
is the sum of the fixed chart weights over the charts containing the endpoint.

The charts are those of `cutoffBrokenLineFamily`, transported through its exact
fiber equivalence with actual rays. The common semilinear-family chart construction
subdivides the endpoint domains into disjoint relative interiors. The
endpoint-chart description follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg
models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (a : ℳ 0) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V) [Finite J]

local notation "domain" t => CutoffDecoratedType.domain c P W S C t

open Classical in
/-- Subdividing each type domain into disjoint charts preserves weighted
evaluation. Different types are summed separately even when their charts coincide.
No geometric assumptions on the chart pieces are required for this identity. -/
theorem cutoffDecoratedEvaluation_eq_sum_charts (k : ℕ)
    (ι : CutoffDecoratedType d ℳ T a v f ε k → Type*) [∀ t, Fintype (ι t)]
    (A : ∀ t, ι t → Set V)
    (hdisj : ∀ t, Pairwise fun i j => Disjoint (A t i) (A t j))
    (hcover : ∀ t, ⋃ j, A t j = domain t) (Q : V) :
    cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q =
      let := Fintype.ofFinite (CutoffDecoratedType d ℳ T a v f ε k)
      ∑ t : CutoffDecoratedType d ℳ T a v f ε k,
        ∑ j : ι t, if Q ∈ A t j then t.decoration else 0 := by
  classical
  let := Fintype.ofFinite (CutoffDecoratedType d ℳ T a v f ε k)
  rw [cutoffDecoratedEvaluation_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Set.ite_mem_eq_sum_of_pairwise_disjoint (A t) (hdisj t) (hcover t) Q t.decoration


section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite K] [Finite O]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

include hf hP hW hS hC

/-- The entire cutoff family has finitely many polyhedral endpoint charts,
indexed by decorated type and convex piece. The equivalence recovers actual rays
and preserves endpoints, types and whole final decorations. Each closed chart
lies in the closure of its type's valid domain; its boundary need not be valid. -/
theorem exists_cutoffDecoratedRay_polyhedralCharts (k : ℕ) :
    ∃ (ι : CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k → Type)
      (_ : ∀ t, Finite (ι t)) (B : ∀ t, ι t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧ B t j ⊆ closure (domain t)) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = domain t) ∧
      ∃ e : (Σ t, Σ j : ι t, intrinsicInterior ℝ (B t j)) ≃
          (Σ Q, CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q),
        (∀ z, (e z).1 = z.2.2.val) ∧
        (∀ z, (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q))
          f c ε P W S C k (e z).1 (e z).2).val = z.1) ∧
        ∀ z, (e z).2.decoration = z.1.decoration := by
  obtain ⟨ι, hι, B, hB, hdisj, hcover, eF, hendpoint, htype⟩ :=
    exists_cutoffBrokenLineFamily_polyhedralCharts d ℳ T a f c ε P W S C
      h w hf hP hW hS hC k
  let E (Q : V) := cutoffBrokenLineFamilyFiberEquiv d ℳ T a f c ε P W S C
    h w hf hP hW hS hC k Q
  let e := eF.trans (Equiv.sigmaCongrRight E)
  have he (z) :
      (cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q))
        f c ε P W S C k (e z).1 (e z).2).val = z.1 :=
    (cutoffBrokenLineFamilyFiberEquiv_type d ℳ T a f c ε P W S C
      h w hf hP hW hS hC k (eF z).1 (eF z).2).trans (htype z)
  refine ⟨ι, hι, B, hB, hdisj, hcover, e, hendpoint, he, fun z => ?_⟩
  exact (cutoffBrokenLineFamilyFiberEquiv_decoration d ℳ T a f c ε P W S C
    h w hf hP hW hS hC k (eF z).1 (eF z).2).trans
      (congrArg CutoffDecoratedType.decoration (htype z))

end Rational

end Mei
