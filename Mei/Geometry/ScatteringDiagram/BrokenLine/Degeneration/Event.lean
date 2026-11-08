/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Boundary
public import Mei.Geometry.Convex.Polyhedron.WallEvent.Regular

/-!
# Closed type limits with exact simultaneous encounters

Exact simultaneous-event supports are generally nonclosed. Nevertheless, at
regular limits their incidence constraints persist just as for closed ambient
walls. The full boundary classification therefore applies without replacing an
event by its chosen wall or losing any of its coincident wall indices.

For a polyhedral incoming source, every regular closed type limit with endpoint
off the walls is in its original full admissible domain. A boundary endpoint
has a terminal wall contact, a wall-singular or prescribed singular contact,
or an incoming tail in a tight tangential source face. These statements concern
the complete original type and path, including its unbounded incoming tail.
They assert neither admissibility of singular boundary paths nor codimension
bounds for the boundary events.

The closed-family interpretation follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2). Exact simultaneous events
use `WallEvent.support`; the proof applies the common full-domain boundary
theorem through the regular-event germ comparison.
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J] [Finite K]
  {T : WallEvent J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (W : J → Set V)
  (S : K → Set V) (C : Set V) {k : ℕ}
  (t : CutoffDecoratedType d ℳ T a v (fun e => e.normal f) Prod.snd k)
  (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j))
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (W j)).direction)
  (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | f j x = c j})
  (hS : ∀ j, TauCeti.IsConvexPolyhedron (S j))

local notation "offset" => fun e : WallEvent J => WallEvent.offset e c
local notation "P" => fun e : WallEvent J => WallEvent.support e W
local notation "wall" => fun e : WallEvent J => Exists.choose (Subtype.property (Prod.fst e))
local notation "D" => domain offset P W S C t

include hW hdir hspan hS

omit hdir hspan hS [Finite K] in
private theorem eventually_mem_wallEvent_support_of_mem_closure (e : WallEvent J)
    {x : V} (hx : x ∈ closure (e.support W)) (hreg : x ∉ singularSupport W) :
    ∀ᶠ y in 𝓝 x, y ∈ W (wall e) → y ∈ e.support W := by
  filter_upwards [e.eventually_mem_support_iff_of_mem_closure W
    (fun j => (hW j).isClosed) hx hreg e.1.property.choose_spec] with y hy hywall
  exact hy.mpr hywall

omit hW hdir hS [Finite J] [Finite K] in
private theorem wallEvent_normal_apply_of_mem (e : WallEvent J)
    {x : V} (hx : x ∈ W (wall e)) : e.normal f x = e.offset c := by
  simpa only [WallEvent.normal_def, WallEvent.offset_def, Set.mem_ofPred_eq] using
    (hspan _).subset (subset_affineSpan ℝ _ hx)

omit hW hspan hS [Finite J] [Finite K] in
private theorem wallEvent_kernel_le_direction (e : WallEvent J) :
    LinearMap.ker (e.normal f).toLinearMap ≤ (affineSpan ℝ (W (wall e))).direction := by
  simpa only [WallEvent.normal_def] using hdir (wall e)

/-- At a regular limit, the original domain with exact simultaneous-event
supports agrees locally with admission of the whole incoming tail. No closedness
of event supports or polyhedral assumption on the incoming source is imposed. -/
theorem eventually_mem_domain_wallEvent_iff_sourceAdmission_of_regular
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path offset Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path offset Q s ∉ S j) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D ↔ ∀ᶠ s : ℝ in atBot, t.path offset Y s ∈ C := by
  apply t.eventually_mem_domain_iff_sourceAdmission_of_regular
    offset P W S C wall hW
    (fun e => e.support_subset W e.1.property.choose_spec)
    (fun e x hx hreg => eventually_mem_wallEvent_support_of_mem_closure W hW e hx hreg)
    (fun e x hx => wallEvent_normal_apply_of_mem f c W hspan e hx)
    (fun e => wallEvent_kernel_le_direction f W hdir e)
    f c hspan hS hQ hoff hregular havoid

/-- A regular closed type limit for exact simultaneous events is an actual
admissible endpoint of that same complete type. The original polyhedral incoming
source is retained, including tails whose base point is outside the source. -/
theorem mem_domain_wallEvent_of_mem_closure_of_regular
    (hC : TauCeti.IsConvexPolyhedron C) {Q : V} (hQ : Q ∈ closure D)
    (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, t.path offset Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → t.path offset Q s ∉ S j) : Q ∈ D := by
  have hnear := t.eventually_mem_domain_wallEvent_iff_sourceAdmission_of_regular
    f c W S C hW hdir hspan hS hQ hoff hregular havoid
  exact (mem_of_mem_nhds hnear).mpr
    (t.path_eventually_mem_of_isConvexPolyhedron offset P W S C hC hQ)

variable {ι : Type*} [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)

local notation "source" => Set.iInter fun j : ι => Set.ofPred fun x : V => g j x ≤ 0
local notation "Dg" => domain offset P W S source t
local notation "F" => fun j => WallEvent.normal (t.itinerary.val.get j) f
local notation "b" => fun j => WallEvent.offset (t.itinerary.val.get j) c
local notation "w" => fun j : Fin t.itinerary.val.length => v (t.history.val j)
local notation "X" => backwardPoint F b w (Fin.last t.itinerary.val.length)

/-- Nonclosed exact event supports produce no extra boundary alternative:
every full-domain frontier has a terminal or singular contact, or the original
incoming tail lies in a tight nonconstant tangential source face. -/
theorem mem_frontier_domain_wallEvent_imp_terminal_or_singular_or_source_face
    {Q : V} (hQ : Q ∈ frontier Dg) :
    (∃ j, Q ∈ W j) ∨
      (∃ s ≤ 0, t.path offset Q s ∈ singularSupport W) ∨
      (∃ j s, s ≤ 0 ∧ t.path offset Q s ∈ S j) ∨
      ∃ j, (g j).linear (v 0) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
        ∀ᶠ s : ℝ in atBot, t.path offset Q s ∈ {x ∈ source | g j x = 0} := by
  apply t.mem_frontier_domain_imp_terminal_or_singular_or_source_face
    offset P W S wall hW
    (fun e => e.support_subset W e.1.property.choose_spec)
    (fun e x hx hreg => eventually_mem_wallEvent_support_of_mem_closure W hW e hx hreg)
    (fun e x hx => wallEvent_normal_apply_of_mem f c W hspan e hx)
    (fun e => wallEvent_kernel_le_direction f W hdir e)
    f c hspan hS g hQ

end Mei.CutoffDecoratedType
