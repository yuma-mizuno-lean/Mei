/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Boundary
public import Mei.Geometry.Convex.Polyhedron.WallEvent.Regular

/-!
# Boundaries of admissible domains with exact simultaneous events

Let each recorded encounter of a backward ray be an exact simultaneous wall
event, with the event's chosen normal and offset and its exact incidence support.
These supports are generally not closed. Nevertheless, at regular limits their
incidence constraints persist just as for closed ambient walls, so the boundary
classification of admissible backward domains applies without replacing an event
by its chosen wall or losing any of its coincident wall indices.

For a convex polyhedral incoming source, every regular limit of admissible
endpoints with endpoint off the walls is admissible. A boundary endpoint has a
terminal wall contact, a wall-singular or prescribed singular contact, or an
incoming tail in a tight tangential source face. Neither admissibility of
singular boundary paths nor codimension bounds for the boundary events are
asserted.

The proofs apply the boundary theorems of
`Mei.Geometry.Convex.Sweep.Admissible.Boundary` through the regular-event germ
comparison `WallEvent.eventually_mem_support_iff_of_mem_closure`. The
closed-family interpretation follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V ι K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι] [Finite K]
  (f : ι → V →L[ℝ] ℝ) (c : ι → ℝ) (W : ι → Set V) (S : K → Set V) (C : Set V)
  {n : ℕ} (e : Fin n → WallEvent ι) (v : Fin (n + 1) → V)
  (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j))
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (W j)).direction)
  (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | f j x = c j})
  (hS : ∀ j, TauCeti.IsConvexPolyhedron (S j))
  (hnormal : ∀ j, (e j).normal f (v j.succ) = (e j).normal f (v j.castSucc))

local notation "F" => fun j => WallEvent.normal (e j) f
local notation "b" => fun j => WallEvent.offset (e j) c
local notation "P" => fun j => WallEvent.support (e j) W
local notation "wall" => fun j => Exists.choose (Subtype.property (Prod.fst (e j)))
local notation "D" => admissibleBackwardDomain F b v P W S C

omit [Finite ι] in
private theorem wallEvent_normal_apply_of_mem
    (hspan : ∀ j, (affineSpan ℝ (W j) : Set V) = {x | f j x = c j}) (j : Fin n)
    {x : V} (hx : x ∈ W (wall j)) : (e j).normal f x = (e j).offset c := by
  simpa only [WallEvent.normal_def, WallEvent.offset_def, Set.mem_ofPred_eq] using
    (hspan _).subset (subset_affineSpan ℝ _ hx)

include hW hdir hspan hS hnormal

/-- At a regular limit, the admissible domain with exact simultaneous-event
supports agrees locally with admission of the whole incoming tail. No closedness
of event supports or polyhedral assumption on the incoming source is imposed. -/
theorem eventually_mem_admissibleBackwardDomain_wallEvent_iff_sourceAdmission_of_regular_limit
    {Q : V} (hQ : Q ∈ closure D) (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, backwardPath F b v Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → backwardPath F b v Q s ∉ S j) :
    ∀ᶠ Y in 𝓝 Q, Y ∈ D ↔ ∀ᶠ s : ℝ in atBot, backwardPath F b v Y s ∈ C :=
  eventually_mem_admissibleBackwardDomain_iff_sourceAdmission_of_regular_limit
    F b v P W S C wall hW
    (fun j => (e j).support_subset W (e j).1.property.choose_spec)
    (fun j x hx hreg => by
      filter_upwards [(e j).eventually_mem_support_iff_of_mem_closure W
        (fun k => (hW k).isClosed) hx hreg (e j).1.property.choose_spec] with y hy hywall
      exact hy.mpr hywall)
    (fun j x hx => wallEvent_normal_apply_of_mem f c W e hspan j hx)
    (fun j => by simpa only [WallEvent.normal_def] using hdir (wall j))
    hnormal f c hspan hS hQ hoff hregular havoid

/-- A regular limit of admissible endpoints with exact simultaneous events is
admissible. The original polyhedral incoming source is retained, including tails
whose base point is outside the source. -/
theorem mem_admissibleBackwardDomain_wallEvent_of_regular_limit
    (hC : TauCeti.IsConvexPolyhedron C) {Q : V} (hQ : Q ∈ closure D)
    (hoff : ∀ j, Q ∉ W j)
    (hregular : ∀ s ≤ 0, backwardPath F b v Q s ∉ singularSupport W)
    (havoid : ∀ j s, s ≤ 0 → backwardPath F b v Q s ∉ S j) : Q ∈ D :=
  (mem_of_mem_nhds
    (eventually_mem_admissibleBackwardDomain_wallEvent_iff_sourceAdmission_of_regular_limit
      f c W S C e v hW hdir hspan hS hnormal hQ hoff hregular havoid)).mpr
    (backwardPath_eventually_mem_of_mem_closure_admissibleBackwardDomain F b v P W S C hC hQ)

variable {κ : Type*} [Finite κ] (g : κ → V →ᴬ[ℝ] ℝ)

local notation "source" => Set.iInter fun j : κ => Set.ofPred fun x : V => g j x ≤ 0
local notation "X" => backwardPoint F b (fun j : Fin n => v (Fin.castSucc j)) (Fin.last n)

/-- Nonclosed exact event supports produce no extra boundary alternative:
every frontier endpoint has a terminal or singular contact, or the original
incoming tail lies in a tight nonconstant tangential source face. -/
theorem mem_frontier_admissibleBackwardDomain_wallEvent_imp_terminal_or_singular_or_sourceFace
    {Q : V} (hQ : Q ∈ frontier (admissibleBackwardDomain F b v P W S source)) :
    (∃ j, Q ∈ W j) ∨
      (∃ s ≤ 0, backwardPath F b v Q s ∈ singularSupport W) ∨
      (∃ j s, s ≤ 0 ∧ backwardPath F b v Q s ∈ S j) ∨
      ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
        ∀ᶠ s : ℝ in atBot, backwardPath F b v Q s ∈ {x ∈ source | g j x = 0} :=
  mem_frontier_admissibleBackwardDomain_imp_terminal_or_singular_or_sourceFace
    F b v P W S wall hW
    (fun j => (e j).support_subset W (e j).1.property.choose_spec)
    (fun j x hx hreg => by
      filter_upwards [(e j).eventually_mem_support_iff_of_mem_closure W
        (fun k => (hW k).isClosed) hx hreg (e j).1.property.choose_spec] with y hy hywall
      exact hy.mpr hywall)
    (fun j x hx => wallEvent_normal_apply_of_mem f c W e hspan j hx)
    (fun j => by simpa only [WallEvent.normal_def] using hdir (wall j))
    hnormal f c hspan hS g hQ

end Mei.Convex
