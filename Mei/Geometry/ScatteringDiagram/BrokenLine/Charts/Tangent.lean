/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rescaling
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration

/-!
# Rescaling complete decorated-type charts

For selected walls through a common center, a complete decorated type has the
same degree history and whole decorations before and after passing to tangent
supports. Its extended path rescales in space and time with unchanged velocities.
At small positive scales the strict incidence domains agree, as do the weak domains
that retain collapsed and terminal encounters. A single scale works for every
complete type at the fixed cutoff and every endpoint in a bounded set.

These are comparisons of the selected-incidence constraints of the existing
closed path charts. They do not identify the full admissible domains: unrecorded
wall avoidance, singular avoidance and incoming-source admission also have to be
compared. In particular, no limiting path is asserted to be admissible.

We apply the backward-itinerary rescaling identities to `CutoffDecoratedType.path`
and use the existing finite complete-type inventory. This is the closed-chart
rescaling used in the study of local broken-line resolutions; see
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (z : V)

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k

/-- The same complete type and its entire incoming half-line are retained when
space and time shrink together about a common center of the selected walls.
The formula is valid even outside the type's admissible endpoint domain. -/
@[simp↓]
theorem path_add_smul (t : Types) (Q : V) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    t.path (fun j => f j z) (z + r • Q) (r * s) = z + r • t.path 0 Q s := by
  simp only [path_def]
  exact backwardPath_add_smul _ z Q _ hr s

variable [Finite J] (P : J → Set V)
  (hP : ∀ j, TauCeti.IsConvexPolyhedron (P j)) (hz : ∀ j, z ∈ P j)
  {K : Set V} (hK : Bornology.IsBounded K)
include hP hz hK

/-- One positive scale bound compares the strict selected-incidence domains
for all complete types and all endpoints in a bounded set simultaneously.
Every recorded encounter is retained, even without a change of degree or velocity. -/
theorem eventually_forall_mem_backwardDomain_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K,
      z + r • Q ∈ backwardDomain (fun j => f (t.itinerary.val.get j))
        (fun j => f (t.itinerary.val.get j) z) (fun j => v (t.history.val j))
        (fun j => P (t.itinerary.val.get j)) ↔
        Q ∈ backwardDomain (fun j => f (t.itinerary.val.get j)) 0 (fun j => v (t.history.val j))
          (fun j => posTangentConeAt (P (t.itinerary.val.get j)) z) := by
  exact eventually_all.mpr fun t =>
    Convex.eventually_forall_mem_backwardDomain_add_smul_iff
      (fun j => f (t.itinerary.val.get j)) (fun j => v (t.history.val j)) z
      (fun j => P (t.itinerary.val.get j))
      (fun j => hP (t.itinerary.val.get j)) (fun j => hz (t.itinerary.val.get j)) hK

/-- A single scale also compares every weak incidence domain in the complete
cutoff inventory, including charts with collapsed and terminal encounters. -/
theorem eventually_forall_mem_weakBackwardDomain_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K,
      z + r • Q ∈ weakBackwardDomain (fun j => f (t.itinerary.val.get j))
        (fun j => f (t.itinerary.val.get j) z) (fun j => v (t.history.val j))
        (fun j => P (t.itinerary.val.get j)) ↔
        Q ∈ weakBackwardDomain (fun j => f (t.itinerary.val.get j)) 0 (fun j => v (t.history.val j))
          (fun j => posTangentConeAt (P (t.itinerary.val.get j)) z) := by
  exact eventually_all.mpr fun t =>
    Convex.eventually_forall_mem_weakBackwardDomain_add_smul_iff
      (fun j => f (t.itinerary.val.get j)) (fun j => v (t.history.val j)) z
      (fun j => P (t.itinerary.val.get j))
      (fun j => hP (t.itinerary.val.get j)) (fun j => hz (t.itinerary.val.get j)) hK

end Mei.CutoffDecoratedType
