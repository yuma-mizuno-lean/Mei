/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration
public import Mei.Geometry.Convex.Sweep.Collision

/-!
# Collisions in closed decorated-ray charts

On the closure of a complete decorated type's valid endpoint domain, a collapsed
encounter interval is either terminal, putting the endpoint on a wall, or
internal, putting the limiting path in singular support. Thus a limiting path
whose endpoint misses the walls and whose encounters remain regular retains
strictly positive elapsed times.

The wall family used for this classification may differ from the encounter
alphabet. Each encounter support need only lie in a corresponding closed wall
with the prescribed normal and offset. This permits exact simultaneous-event
supports, which are usually not closed. All coefficient histories, source
conditions and avoidance conditions remain in the original type domain.

These results classify loss of strict time order; they do not classify every
boundary event or assert admissibility of every limiting path. We combine
`backwardTime_eq_zero_imp_terminal_or_singularSupport` with the existing
`CutoffDecoratedType.path`. The closed-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

open Set Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P W : J → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k)
  (A : ι → Set V) (wall : J → ι)
  (hclosed : ∀ i, IsClosed (A i)) (hP : ∀ j, P j ⊆ A (wall j))
  (hheight : ∀ j x, x ∈ A (wall j) → f j x = c j)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)
local notation "τ" => backwardParameter F b
  (fun j : Fin t.itinerary.val.length => v (t.history.val j))
local notation "D" => domain c P W S C t

include hclosed hP hheight

/-- Every collapsed interval of a closed decorated type is a terminal wall
encounter or an interior singular encounter of its actual limiting path.
The ambient walls are closed, but selected event supports may be nonclosed. -/
theorem backwardTime_eq_zero_imp_terminal_or_singularSupport
    {Q : V} (hQ : Q ∈ closure D) (j : Fin t.itinerary.val.length)
    (ht : backwardTime F b (fun j => u j.castSucc) j Q = 0) :
    (j.val = 0 ∧ Q ∈ A (wall (t.itinerary.val.get j))) ∨
      t.path c Q (τ j.succ Q) ∈ singularSupport A := by
  have hD : D ⊆ backwardDomain F b (fun j => u j.castSucc)
      (fun j => A (wall (t.itinerary.val.get j))) := by
    intro X hX
    rw [domain_def] at hX
    have hm := (mem_backwardDomain ..).mp
      (admissibleBackwardDomain_subset_backwardDomain _ _ _ _ _ _ _ hX)
    apply (mem_backwardDomain ..).mpr
    intro l
    exact ⟨(hm l).1, hP _ (hm l).2⟩
  have he := Convex.backwardTime_eq_zero_imp_terminal_or_singularSupport F b
    (fun j => u j.castSucc) A (fun j => wall (t.itinerary.val.get j))
    (fun j => hheight (t.itinerary.val.get j)) hclosed hD hQ j ht
  have hp := backwardPath_apply_parameter F b u
    (t.backwardTime_nonneg c P W S C hQ) j.succ
  simp only [Fin.snoc_castSucc] at hp he
  rwa [path_def, hp]

/-- A limiting endpoint off the walls, with every recorded encounter outside
singular support, has no collapsed intervals. This conclusion concerns time
order and does not assume the limiting ray is already admissible. -/
theorem backwardTime_pos_of_notMem_singularSupport
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin t.itinerary.val.length,
      t.path c Q (τ j.succ Q) ∉ singularSupport A)
    (j : Fin t.itinerary.val.length) :
    0 < backwardTime F b (fun j => u j.castSucc) j Q := by
  rcases eq_or_lt_of_le (t.backwardTime_nonneg c P W S C hQ j) with hz | hpos
  · rcases t.backwardTime_eq_zero_imp_terminal_or_singularSupport c P W S C A wall
      hclosed hP hheight hQ j hz.symm with ⟨_, hwall⟩ | hsing
    · exact (hendpoint _ hwall).elim
    · exact (hregular j hsing).elim
  · exact hpos

end Mei.CutoffDecoratedType
