/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Basic
public import Mei.Geometry.Convex.Sweep.Admissible.Contact
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Transverse contacts in closed decorated-type paths

A wall contact appearing strictly between recorded encounters in a closed
decorated-type path is singular whenever the segment direction is transverse
to the wall. This includes the open incoming tail and unchanged-direction
encounters. It is a boundary-event restriction on the existing closed paths,
not an assertion that boundary paths are admissible.

The full type domain retains its source, whole decorations and avoidance
conditions. The proof uses the affine path extension and persistence of
transverse relative-interior contacts. This is the closed-family interpretation
of Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

open Set Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "τ" => backwardParameter F b
  (fun j : Fin t.itinerary.val.length => u (Fin.castSucc j))

/-- Every transverse wall contact on an open segment of a limiting complete
type path lies in singular support. The last segment index is the incoming
half-line and imposes no upper bound on the positive displacement. -/
theorem path_mem_singularSupport_of_transverse_contact
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (j : Fin (t.itinerary.val.length + 1)) {s : ℝ} (hs : 0 < s)
    (hs' : ∀ e : Fin t.itinerary.val.length, j = e.castSucc →
      s < backwardTime F b (fun l => u l.castSucc) e Q)
    (a : O) (ν : V →L[ℝ] ℝ) (z : ℝ)
    (hspan : (affineSpan ℝ (W a) : Set V) = {x | ν x = z})
    (hv : ν (u j) ≠ 0) (hhit : t.path c Q (τ j Q - s) ∈ W a) :
    t.path c Q (τ j Q - s) ∈ singularSupport W := by
  have hdomain : Q ∈ closure (admissibleBackwardDomain F b u
      (fun e => P (t.itinerary.val.get e)) W S C) := by
    simpa only [domain_def, Fin.snoc_castSucc] using hQ
  rw [path_def] at hhit ⊢
  apply mem_singularSupport.mpr
  left
  refine ⟨a, ?_⟩
  rcases Fin.eq_castSucc_or_eq_last j with ⟨e, rfl⟩ | rfl
  · exact backwardPath_mem_intrinsicFrontier_of_segment_contact F b u
      (fun e => P (t.itinerary.val.get e)) W S C hdomain e hs (hs' e rfl)
      a ν z hspan hv hhit
  · exact backwardPath_mem_intrinsicFrontier_of_incoming_contact F b u
      (fun e => P (t.itinerary.val.get e)) W S C hdomain hs a ν z hspan hv hhit

end Mei.CutoffDecoratedType
