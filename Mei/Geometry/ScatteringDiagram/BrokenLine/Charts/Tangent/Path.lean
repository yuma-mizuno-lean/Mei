/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Charts.Tangent
public import Mei.Geometry.Convex.Sweep.Rescaling.Path

/-!
# Local wall avoidance in rescaled complete-type charts

A single small positive scale compares the local wall and singular avoidance
constraints for every complete decorated type at a fixed cutoff.
The comparison is uniform over bounded endpoints and bounded time windows.
Every recorded encounter time is retained, including unchanged-degree events,
and the full singular support is compared. Walls missing the center disappear.

These are the local path constraints needed to compare a closed chart with an
incident tangent chart while fixing its exterior pieces. They complement the
selected-incidence constraints in
`Mei.CutoffDecoratedType.eventually_forall_mem_backwardDomain_add_smul_iff`.
They do not compare unbounded incoming tails, source admission or exterior pieces,
and do not assert admissibility of a boundary path.
The closed-chart interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  [Finite J] [Finite O] (z : V) (W : O → Set V)
  (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j))
  {K : Set V} {I : Set ℝ} (hK : Bornology.IsBounded K) (hI : Bornology.IsBounded I)

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "F" t:max => fun j =>
  f (List.get (Subtype.val (CutoffDecoratedType.itinerary t)) j)
local notation "u" t:max => fun j =>
  v (Fin.snoc (α := fun _ => Γ) (Subtype.val (CutoffDecoratedType.history t)) 0 j)
local notation "τ" t:max c:max => backwardParameter (F t) c (fun j => (u t) (Fin.castSucc j))
local notation "TW" => fun j : {j | z ∈ W j} => posTangentConeAt (W j) z

include hW hK hI

/-- At a single scale uniform over the complete cutoff inventory, the local
no-extra-encounter and regularity constraints agree with those of the incident
tangent supports. Only recorded encounter times are excepted from wall avoidance;
no time is excepted from singular avoidance. -/
theorem eventually_forall_path_avoids_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K,
      ((∀ s ∈ I, (∀ j : Fin t.itinerary.val.length,
          r * s ≠ (τ t (fun j => (F t) j z)) j.succ (z + r • Q)) →
          ∀ b, t.path (fun j => f j z) (z + r • Q) (r * s) ∉ W b) ∧
        ∀ s ∈ I, t.path (fun j => f j z) (z + r • Q) (r * s) ∉ singularSupport W) ↔
      ((∀ s ∈ I, (∀ j : Fin t.itinerary.val.length, s ≠ (τ t 0) j.succ Q) →
          ∀ b, t.path 0 Q s ∉ TW b) ∧
        ∀ s ∈ I, t.path 0 Q s ∉ singularSupport TW) := by
  have hm : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K, ∀ s ∈ I, ∀ b,
      t.path (fun j => f j z) (z + r • Q) (r * s) ∈ W b ↔
        z ∈ W b ∧ t.path 0 Q s ∈ posTangentConeAt (W b) z := by
    apply eventually_all.mpr
    intro t
    simpa only [path_def, Pi.zero_def] using
      Convex.eventually_forall_backwardPath_mem_add_smul_iff
        (F t) (u t) z W hW hK hI
  have hs : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K, ∀ s ∈ I,
      t.path (fun j => f j z) (z + r • Q) (r * s) ∈ singularSupport W ↔
        t.path 0 Q s ∈ singularSupport TW := by
    apply eventually_all.mpr
    intro t
    simpa only [path_def, Pi.zero_def] using
      Convex.eventually_forall_backwardPath_mem_singularSupport_add_smul_iff
        (F t) (u t) z W hW hK hI
  filter_upwards [hm, hs, self_mem_nhdsWithin] with r hr hsing hrpos
  intro t Q hQ
  have htimes (s : ℝ) :
      (∀ j : Fin t.itinerary.val.length,
        r * s ≠ (τ t (fun j => (F t) j z)) j.succ (z + r • Q)) ↔
        ∀ j : Fin t.itinerary.val.length, s ≠ (τ t 0) j.succ Q := by
    simp only [backwardParameter_add_smul, ne_eq, mul_right_inj' hrpos.ne']
  constructor
  · rintro ⟨hwall, hreg⟩
    refine ⟨?_, fun s hs => fun hh => hreg s hs ((hsing t Q hQ s hs).mpr hh)⟩
    intro s hs htime b hb
    exact hwall s hs ((htimes s).mpr htime) b.val
      ((hr t Q hQ s hs b.val).mpr ⟨b.property, hb⟩)
  · rintro ⟨hwall, hreg⟩
    refine ⟨?_, fun s hs => fun hh => hreg s hs ((hsing t Q hQ s hs).mp hh)⟩
    intro s hs htime b hb
    obtain ⟨hzb, hb⟩ := (hr t Q hQ s hs b).mp hb
    exact hwall s hs ((htimes s).mp htime) ⟨b, hzb⟩ hb

end Mei.CutoffDecoratedType
