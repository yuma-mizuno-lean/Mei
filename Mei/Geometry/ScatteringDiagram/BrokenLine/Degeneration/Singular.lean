/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic
public import Mei.Geometry.Convex.Sweep.Singular.Stability

/-!
# Singular contacts at decorated-type boundaries

A frontier point of the full domain of a cutoff decorated type either lies on
the frontier of its other endpoint constraints or its extended path meets a
singular cell. In the latter case an actual nonpositive contact parameter is
retained, including on the incoming half-line. In particular a regular limiting
path cannot contribute a boundary solely through loss of singular avoidance.

The other constraints retain selected support incidence, positive elapsed times,
absence of unrecorded wall encounters, eventual incoming-source admission and
an allowed endpoint. This separates the singular-avoidance case without claiming
that all boundary paths are admissible or classifying the remaining constraints.
The entire decorated history and incoming tail remain attached to the type.

We apply `eventually_mem_backwardSingularAvoidanceDomain` to the existing closed
path extension. The endpoint-chart interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite K]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "A" => fun j => P (t.itinerary.val.get j)
local notation "w" => fun j => u (Fin.castSucc j)

/-- Every full type-domain boundary is a boundary of the remaining geometric
constraints or a genuine singular contact of the extended negative half-line.
The singular cells need only be convex polyhedra; selected supports, walls and
the incoming source may be arbitrary sets. -/
theorem mem_frontier_domain_imp_singular_or_mem_frontier
    (hS : ∀ a, TauCeti.IsConvexPolyhedron (S a)) {Q : V}
    (hQ : Q ∈ frontier (domain c P W S C t)) :
    (∃ a s, s ≤ 0 ∧ t.path c Q s ∈ S a) ∨
      Q ∈ frontier
        ((backwardAvoidanceDomain F b w A W ∩
          backwardIncomingDomain F b w A (u (Fin.last t.itinerary.val.length)) C W) ∩
            {Q' | ∀ j, Q' ∉ W j}) := by
  by_cases hcontact : ∃ a s, s ≤ 0 ∧ t.path c Q s ∈ S a
  · exact Or.inl hcontact
  · right
    have hsub : domain c P W S C t ⊆
        (backwardAvoidanceDomain F b w A W ∩
          backwardIncomingDomain F b w A (u (Fin.last t.itinerary.val.length)) C W) ∩
            {Q' | ∀ j, Q' ∉ W j} := by
      intro Q' hQ'
      obtain ⟨hfinite, hincoming, _, hoff⟩ :=
        (mem_admissibleBackwardDomain ..).mp ((t.mem_domain c P W S C Q').mp hQ')
      exact ⟨⟨hfinite, hincoming⟩, hoff⟩
    refine ⟨closure_mono hsub (frontier_subset_closure hQ), fun hint => ?_⟩
    have havoid : ∀ a s, s ≤ 0 → backwardPath F b u Q s ∉ S a := by
      simpa only [path_def, not_exists, not_and] using hcontact
    have hnear := eventually_mem_backwardSingularAvoidanceDomain F b u A S hS
      (t.backwardTime_nonneg c P W S C (frontier_subset_closure hQ)) havoid
    apply hQ.2
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnear, mem_interior_iff_mem_nhds.mp hint] with Q' hnear hother
    apply (t.mem_domain c P W S C Q').mpr
    apply (mem_admissibleBackwardDomain ..).mpr
    exact ⟨hother.1.1, hother.1.2,
      hnear (backwardAvoidanceDomain_subset_backwardDomain F b w A W hother.1.1), hother.2⟩

end Mei.CutoffDecoratedType
