/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Recursion
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Last-change recursions with generic straight inputs

One exceptional arrangement of outgoing endpoints makes the full weighted
last-change recursion read only generic incoming points for a prescribed
arrangement. The refinement works for every retained outgoing degree. It is
chosen before the coefficients, propagation maps, sources and encounter list.
Each encounter uses one displacement for all its compatible incoming degrees;
the displacement may be arbitrarily small.

The incoming points are the actual straight cuts of the decorated rays. No
perturbation of their velocities or replacement of their incoming histories is
needed. Whole homogeneous coefficients, zero terms, unchanged-degree encounters
and changes with zero spatial projection retain their existing conventions.
The recursion concerns nonzero final relative degrees; a source term must still
be supplied separately in degree zero.

We combine the finite last-change recursion with
`Convex.exists_forall_eventually_isGeneric_sweepProjection`. The backward-ray
interpretation follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J] [Finite K] [Finite I]

open Classical in
/-- Refine outgoing endpoint exceptions so the full last-change recurrence reads
its lower-degree evaluations at generic straight incoming cuts. One displacement
at each encounter works for every compatible retained input degree, including
terms whose coefficient vanishes. The refinement is uniform in the output degree
and independent of the coefficient data and of the chosen encounter inventory. -/
theorem exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange_generic
    (d : PositiveDegrees Γ) (k : ℕ) (A : ExceptionalArrangement V)
    (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
        (T : J → Module.End R M) (a : ℳ 0) (ε : J → SignType)
        (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)
        (q : Γ) (_hq : q ∈ d.cutoff k) (_hq0 : q ≠ 0)
        (E : Finset J)
        (_hT : ∀ e ∈ E, ∀ x ∈ ℳ q, (DirectSum.decompose ℳ (T e x) q : M) = x)
        (_hP : ∀ j, P j ⊆ ⋃ b, W b) (_hclosedW : ∀ j, IsClosed (W j))
        (_hclosedS : ∀ j, IsClosed (S j)) (s : J → ℝ) (_hinj : Set.InjOn s E)
        (_hE : ∀ e ∈ E, 0 < s e ∧ f e (v q) ≠ 0 ∧ SignType.sign (f e (v q)) = ε e ∧
          f e (Q + s e • v q) = c e ∧ Q + s e • v q ∈ P e)
        (_hhit : ∀ e (u : ℝ), 0 < u → f e (v q) ≠ 0 →
          SignType.sign (f e (v q)) = ε e → f e (Q + u • v q) = c e →
          Q + u • v q ∈ P e → e ∈ E ∧ s e = u)
        (_hplane : ∀ e ∈ E, ∀ j, Q + s e • v q ∈ W j → ∀ y ∈ W j, f e y = c e)
        (_hWray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∈ W j → ∃ e ∈ E, s e = u)
        (_hSray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∉ S j),
      ∀ θ > 0, ∃ η : J → ℝ,
        (∀ e ∈ E, 0 < η e ∧ η e < θ ∧
          ∀ r ∈ d.cutoff k, f e (v q) = f e (v r) →
            A.IsGeneric (Q + s e • v q + η e • v r)) ∧
        (DirectSum.decompose ℳ
          (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
          ∑ e ∈ E, ∑ r ∈ (d.finite_cutoff k).toFinset with
              r ≠ q ∧ q - r ∈ d.monoid ∧ f e (v q) = f e (v r),
            (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
              (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
                (Q + s e • v q + η e • v r)) r)) q : M) := by
  classical
  let Z := {z : J × d.cutoff k × d.cutoff k // f z.1 (v z.2.2.val) ≠ 0}
  obtain ⟨F, hF⟩ := exists_forall_eventually_isGeneric_sweepProjection A
    (fun z : Z => f z.val.1) (fun z => c z.val.1)
    (fun z => (f z.val.1 (v z.val.2.1.val))⁻¹ • v z.val.2.1.val)
    (fun z => v z.val.2.2.val) (fun z => z.property)
  refine ⟨F, fun Q hQ ℳ _ T a ε P W S C q hq hq0 E hT hP hclosedW hclosedS s hinj
    hE hhit hplane hWray hSray θ hθ => ?_⟩
  apply exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange_of_eventually
    hq hq0 E hT hP hclosedW hclosedS s hinj hE hhit hplane hWray hSray
    (fun e η => ∀ r ∈ d.cutoff k, f e (v q) = f e (v r) →
      A.IsGeneric (Q + s e • v q + η • v r)) ?_ θ hθ
  intro e he
  -- The geometric refinement simultaneously controls every transverse incoming
  -- degree, so no finiteness of coefficient supports is needed here.
  filter_upwards [hF Q hQ] with η hη r hr hnormal
  have htrans : f e (v r) ≠ 0 := hnormal ▸ (hE e he).2.1
  let z : Z := ⟨(e, ⟨q, hq⟩, ⟨r, hr⟩), htrans⟩
  have hheight := (hE e he).2.2.2.1
  simpa only [z,
    ContinuousLinearMap.sweepProjection_inv_smul_eq_add_smul _ (hE e he).2.1 hheight]
    using hη z

end Mei.CutoffDecoratedRay
