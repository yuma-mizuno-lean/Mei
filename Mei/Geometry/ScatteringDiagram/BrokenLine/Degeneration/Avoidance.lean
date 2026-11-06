/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration.Collision
public import Mei.Geometry.Convex.Sweep.Admissible.Avoidance

/-!
# No extra encounters in regular limits of decorated rays

For a complete decorated type, a limiting path with an allowed endpoint and
no singular encounters still records every wall encounter, including on the
unbounded incoming tail. Tangential contacts introduce no additional exception:
the whole-component history preserves normal velocity at recorded encounters.
Together with the collision theorem, this excludes loss of wall avoidance as
an independent boundary event away from terminal and singular degenerations.

The result uses the original full type domain and its existing path extension.
Selected event supports may be nonclosed subsets of the closed ambient walls;
no source, coefficient, degree or unchanged-direction records are discarded.
It does not assert that selected-event membership or source admission is open
at the limiting endpoint. The closed-family interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
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

/-- A regular limit of a complete decorated type has no unrecorded wall
encounters. This covers transverse and tangential contacts on every finite
segment and on the entire incoming half-line, including zero spatial directions. -/
theorem path_avoids_walls_of_regular
    (wall : J → O) (hclosed : ∀ a, IsClosed (W a))
    (hP : ∀ j, P j ⊆ W (wall j))
    (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)
    (ν : O → V →L[ℝ] ℝ) (z : O → ℝ)
    (hspan : ∀ a, (affineSpan ℝ (W a) : Set V) = {x | ν a x = z a})
    {Q : V} (hQ : Q ∈ closure (domain c P W S C t))
    (hoff : ∀ a, Q ∉ W a)
    (hregular : ∀ s ≤ 0, t.path c Q s ∉ singularSupport W) :
    ∀ a s, s < 0 → (∀ j : Fin t.itinerary.val.length, s ≠ τ j.succ Q) →
      t.path c Q s ∉ W a := by
  have h0 := t.backwardTime_nonneg c P W S C hQ
  have hτ (j : Fin (t.itinerary.val.length + 1)) : τ j Q ≤ 0 := by
    simpa using antitone_backwardParameter F b (fun j => u j.castSucc) Q h0 (Fin.zero_le j)
  have hpos := t.backwardTime_pos_of_notMem_singularSupport c P W S C W wall
    hclosed hP hheight hQ hoff (fun j => by
      simpa only [Fin.snoc_castSucc] using hregular (τ j.succ Q) (hτ _))
  have htrans (j : Fin t.itinerary.val.length) : F j (u j.succ) ≠ 0 := by
    have hn := ((mem_decoratedHistorySupport ℳ (fun j => T (t.itinerary.val.get j))
      0 a v F (fun j => ε (t.itinerary.val.get j)) t.history.val).mp t.history.property).2 j |>.1
    intro hz
    have hz' : F j (u j.castSucc) = 0 := by simpa only [Fin.snoc_castSucc, hn] using hz
    have hp := hpos j
    simp only [Fin.snoc_castSucc] at hz'
    simp only [backwardTime_apply, Fin.snoc_castSucc, hz', div_zero, lt_self_iff_false] at hp
  have havoid := backwardPath_notMem_wall_of_regular_limit F b u
    (fun j => P (t.itinerary.val.get j)) W S C
    (fun j => wall (t.itinerary.val.get j)) hclosed
    (fun j => hP (t.itinerary.val.get j)) (fun j => hheight (t.itinerary.val.get j))
    htrans ν z hspan (by simpa only [domain_def] using hQ) hoff
    (by simpa only [path_def] using hregular)
  rw [path_def, backwardPath_eq_backwardRay F b u Q hpos]
  simp only [FiniteAffineRay.toContinuousMap_apply]
  apply (backwardRay_avoids_iff F b u Q hpos W).mpr
  constructor
  · intro j a s hs hs'
    have ha := havoid j.castSucc hs (fun e he => by
      have he' : j = e := Fin.castSucc_injective _ he
      simpa only [← he'] using hs') a
    rwa [backwardPath_apply_segment F b u h0 j hs.le hs'.le] at ha
  · intro a s hs
    have ha := havoid (Fin.last _) hs (fun e he => (Fin.castSucc_ne_last e he.symm).elim) a
    rwa [backwardPath_apply_incoming F b u h0 hs.le] at ha

end Mei.CutoffDecoratedType
