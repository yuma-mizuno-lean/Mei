/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rescaling.Incoming
public import Mei.Geometry.Convex.Sweep.Admissible.Source
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic

/-!
# Incoming-source constraints of rescaled complete types

One positive scale bound compares the full incoming-source condition of every
complete decorated type at a fixed cutoff, uniformly on bounded endpoint sets.
The comparison retains the original global source and each type's last
reconstructed point. It uses the tangent cone of the source's ray-admission
domain, which can contain bases outside the source itself.

At a center in the closure of an actual type domain, persistence of incoming
admission supplies the center condition. The rescaled source constraint is then
given explicitly by the tight source inequalities tangent to the incoming
direction. This includes tangential source-face degenerations, empty encounter
words, and degree changes invisible in the spatial projection.

These theorems compare the source constraint on the unbounded incoming tail;
other incidence and avoidance constraints remain separate. They do not assert
admissibility of boundary paths. The closed-chart interpretation follows
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
  [Finite J] (z : V) {K : Set V} (hK : Bornology.IsBounded K)

local notation "Types" => CutoffDecoratedType d ℳ T a v f ε k
local notation "F(" t ")" => fun j =>
  f (List.get (Subtype.val (CutoffDecoratedType.itinerary t)) j)
local notation "u(" t ")" => fun j => v (Subtype.val (CutoffDecoratedType.history t) j)
local notation "X(" t ")" => backwardPoint F(t) 0 u(t)
  (Fin.last (List.length (Subtype.val (CutoffDecoratedType.itinerary t))))
local notation "D(" C ")" => Set.ofPred fun x : V => ∀ᶠ s : ℝ in atTop, x + s • v 0 ∈ C

include hK in
/-- The original source-admission condition of every complete cutoff type
agrees with its tangent-domain test at small positive scales, with one bound
for all types and all endpoints in the given bounded set. -/
theorem eventually_forall_path_eventually_mem_add_smul_iff
    (C : Set V) (hC : TauCeti.IsConvexPolyhedron C) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K,
      (∀ᶠ s : ℝ in atBot, t.path (fun j => f j z) (z + r • Q) s ∈ C) ↔
        z ∈ D(C) ∧ X(t) Q ∈ posTangentConeAt D(C) z := by
  apply eventually_all.mpr
  intro t
  simpa only [path_def, Fin.snoc_castSucc, Fin.snoc_last] using
    Convex.eventually_forall_backwardPath_eventually_mem_add_smul_iff F(t)
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)) z C hC hK

include hK in
/-- At a center approached by actual realizations, the incoming-source test
for every rescaled complete type consists exactly of the tight tangential
source inequalities. Center admission follows from the given actual type's
closed-limit persistence; no source or boundary-admissibility assumption is added. -/
theorem eventually_forall_path_eventually_mem_add_smul_iff_active_of_mem_closure
    {ι A B : Type*} [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)
    (P : J → Set V) (W : A → Set V) (S : B → Set V)
    (t₀ : Types)
    (hz : z ∈ closure (domain (fun j => f j z) P W S {x | ∀ j, g j x ≤ 0} t₀)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ t : Types, ∀ Q ∈ K,
      (∀ᶠ s : ℝ in atBot, ∀ j,
        g j (t.path (fun j => f j z) (z + r • Q) s) ≤ 0) ↔
        ∀ j, (g j).linear (v 0) = 0 → g j z = 0 → (g j).contLinear (X(t) Q) ≤ 0 := by
  have hsource := backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain F(t₀)
    (fun j => f (t₀.itinerary.val.get j) z)
    (fun j => v (Fin.snoc (α := fun _ => Γ) t₀.history.val 0 j))
    (fun j => P (t₀.itinerary.val.get j)) W S {x | ∀ j, g j x ≤ 0}
    (TauCeti.isConvexPolyhedron_setOf_forall g) (by simpa only [domain_def] using hz)
  rw [backwardPath_eventually_mem_iff] at hsource
  have hcenter : backwardPoint F(t₀) (fun j => f (t₀.itinerary.val.get j) z)
      u(t₀) (Fin.last t₀.itinerary.val.length) z = z := by
    simpa only [zero_smul, add_zero] using
      backwardPoint_add_smul F(t₀) u(t₀) z (0 : V) 0 (Fin.last t₀.itinerary.val.length)
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hcenter, mem_ofPred_eq] at hsource
  apply eventually_all.mpr
  intro t
  simpa only [path_def, Fin.snoc_castSucc, Fin.snoc_last] using
    Convex.eventually_forall_backwardPath_eventually_mem_add_smul_iff_active F(t)
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)) z hK g
        (by simpa only [Fin.snoc_last] using hsource)

end Mei.CutoffDecoratedType
