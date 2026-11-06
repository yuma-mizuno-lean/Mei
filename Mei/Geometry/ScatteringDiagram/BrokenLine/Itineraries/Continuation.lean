/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration

/-!
# Continuous continuation of complete decorated rays

Away from a finite exceptional arrangement, all rays at an endpoint continue
uniquely over one convex open neighborhood, preserving their complete decorated
types. Each continued path varies continuously in the compact-open topology.
Thus a continuous motion of endpoints deforms the entire ray, including its
incoming tail, without changing any recorded encounter or homogeneous component.
Distinct types remain separate even when their geometric paths coincide.

The exceptional arrangement is the existing common membership arrangement of
the full type domains. Continuity follows from the backward hinge path of each
type; the continuation consists of actual admissible rays throughout the
neighborhood. No admissibility of paths at its boundary is asserted.

The endpoint deformation viewpoint follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ} [Finite J]
  (c : J → ℝ) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "Rays(" Q ")" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "typeOf(" Q ")" => cutoffDecoratedRayFiberEquiv d ℳ T a v f c ε P W S C k Q

/-- A family of actual rays of one complete type depends continuously on its
endpoints in compact-open path space. No rationality or genericity is required;
the encounter index type is arbitrary finite, while the parameter space and
obstacle index types are unrestricted. -/
theorem CutoffDecoratedRay.continuous_of_type_eq {X : Type*} [TopologicalSpace X]
    {Q : X → V} (r : ∀ x, Rays(Q x)) (t : Types) (hQ : Continuous Q)
    (ht : ∀ x, (typeOf(Q x) (r x)).val = t) :
    Continuous (fun x => (r x).realization.2.ray.toContinuousMap) := by
  have hpath (x : X) :
      (r x).realization.2.ray.toContinuousMap = t.path c (Q x) := by
    rw [← ht x, cutoffDecoratedRayFiberEquiv_apply_val, CutoffDecoratedType.path_def,
      AdmissibleRayRealization.toContinuousMap_eq_backwardPath]
  simpa only [hpath, Function.comp_def] using (t.path c).continuous.comp hQ

section Rational

variable (d ℳ T a f ε) {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite K] [Finite I]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C) (k : ℕ)

local notation "Types'" => CutoffDecoratedType d ℳ T a (fun q => i (w q)) f ε k
local notation "Rays'(" Q ")" =>
  CutoffDecoratedRay d ℳ T a (fun q => i (w q)) f c ε P W S C k Q
local notation "typeOf'(" Q ")" =>
  cutoffDecoratedRayFiberEquiv d ℳ T a (fun q => i (w q)) f c ε P W S C k Q

include hf hP hW hS hC

/-- Off one finite arrangement containing every complete type-domain frontier,
all actual cutoff rays continue over a common convex open neighborhood. There is
exactly one family of fiber bijections preserving complete types, and its paths
vary continuously in compact-open topology. The full incoming source and all
avoidance constraints remain those of the original global ray family. -/
theorem exists_cutoffDecoratedRay_continuousContinuation :
    ∃ E : ExceptionalArrangement V,
      (∀ t : Types', frontier (CutoffDecoratedType.domain c P W S C t) ⊆
        {Q | ¬ E.IsGeneric Q}) ∧
      ∀ Q, E.IsGeneric Q → ∃ U : Set V,
        IsOpen U ∧ Convex ℝ U ∧ Q ∈ U ∧
        ∃! e : ∀ Y : U, Rays'(Q) ≃ Rays'(Y.val),
          (∀ Y r, (typeOf'(Y.val) (e Y r)).val = (typeOf'(Q) r).val) ∧
          ∀ r, Continuous (fun Y : U => (e Y r).realization.2.ray.toContinuousMap) := by
  obtain ⟨E, hfrontier, hstable⟩ := exists_cutoffDecoratedRay_membershipArrangement
    d ℳ T a f c ε P W S C h w hf hP hW hS hC k
  refine ⟨E, hfrontier, fun Q hQ => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hstable Q hQ)
  let U := Metric.ball Q δ
  have hex (Y : U) : ∃ e : Rays'(Q) ≃ Rays'(Y.val),
      ∀ r, (typeOf'(Y.val) (e r)).val = (typeOf'(Q) r).val :=
    hball Y.val Y.property
  choose e he using hex
  refine ⟨U, Metric.isOpen_ball, convex_ball Q δ, Metric.mem_ball_self hδ,
    e, ⟨he, ?_⟩, ?_⟩
  · intro r
    exact CutoffDecoratedRay.continuous_of_type_eq c P W S C (fun Y : U => e Y r)
      (typeOf'(Q) r).val continuous_subtype_val (fun Y => he Y r)
  · intro e' he'
    funext Y
    apply Equiv.ext
    intro r
    apply typeOf'(Y.val).injective
    exact Subtype.ext ((he'.1 Y r).trans (he Y r).symm)

end Rational

end Mei
