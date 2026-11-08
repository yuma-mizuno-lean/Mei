/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Degeneration
public import Mei.Geometry.Convex.Sweep.Boundary

/-!
# Selected-support boundaries in closed decorated-ray charts

For a complete decorated type, forget avoidance and source conditions and retain
only positive elapsed times and incidence with selected ambient walls. A boundary
of this incidence domain is a terminal or singular encounter of the type's
actual limiting path. At limiting endpoints off the walls whose recorded
encounters are regular, these incidence constraints persist on a neighborhood.

The selected event supports may be nonclosed, as for exact simultaneous events;
they need only lie in closed ambient walls spanning their prescribed supporting
hyperplanes. All coefficient histories and incoming tails remain those of the
original type. These results classify the selected-wall incidence constraints,
not the additional avoidance and incoming-source constraints of the full domain.

We apply the geometric incidence-boundary theorem to the existing continuous
`CutoffDecoratedType.path`. The closed-chart interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedType

variable {R M Γ V J K ι O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {ε : J → SignType} {k : ℕ}
  (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (t : CutoffDecoratedType d ℳ T a v f ε k)
  (A : ι → Set V) (wall : J → ι)
  (hclosed : ∀ i, IsClosed (A i)) (hP : ∀ j, P j ⊆ A (wall j))
  (hheight : ∀ j x, x ∈ A (wall j) → f j x = c j)
  (hdir : ∀ j, LinearMap.ker (f j).toLinearMap ≤ (affineSpan ℝ (A (wall j))).direction)

local notation "F" => fun j => f (t.itinerary.val.get j)
local notation "b" => fun j => c (t.itinerary.val.get j)
local notation "u" => fun j : Fin t.itinerary.val.length => v (t.history.val j)
local notation "τ" => backwardParameter F b u
local notation "D" => domain c P W S C t
local notation "B" => backwardDomain F b u (fun j => A (wall (t.itinerary.val.get j)))

include hclosed hheight hdir

/-- A boundary of a type's ambient selected-incidence domain is terminal or
singular along its path extension. The endpoint need not belong to the closure
of the full admissible domain. -/
theorem mem_frontier_backwardDomain_imp_terminal_or_path_mem_singularSupport
    {Q : V} (hboundary : Q ∈ frontier B) :
    (∃ j : Fin t.itinerary.val.length,
      j.val = 0 ∧ Q ∈ A (wall (t.itinerary.val.get j))) ∨
      ∃ j : Fin t.itinerary.val.length,
        t.path c Q (τ j.succ Q) ∈ singularSupport A := by
  rcases Convex.mem_frontier_backwardDomain_imp_terminal_or_singularSupport F b u
    A (fun j => wall (t.itinerary.val.get j))
    (fun j => hheight (t.itinerary.val.get j))
    (fun j => hdir (t.itinerary.val.get j)) hclosed hboundary with ht | ⟨j, hj⟩
  · exact Or.inl ht
  · right
    refine ⟨j, ?_⟩
    have hnonneg : ∀ l, 0 ≤ backwardTime F b u l Q :=
      backwardTime_nonneg_of_mem_closure F b u
        (fun X hX l => ((mem_backwardDomain ..).mp hX l).1.le) hboundary.1
    have hp := backwardPath_apply_parameter F b
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j))
      (by simpa only [Fin.snoc_castSucc] using hnonneg) j.succ
    simp only [Fin.snoc_castSucc] at hp
    rwa [path_def, hp]

include hP

/-- At a regular limiting endpoint, the strict ambient-wall incidence
constraints hold throughout a neighborhood. This says nothing about new
unrecorded encounters or admission to the incoming source at nearby endpoints. -/
theorem mem_interior_backwardDomain_of_notMem_singularSupport
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin t.itinerary.val.length,
      t.path c Q (τ j.succ Q) ∉ singularSupport A) :
    Q ∈ interior B := by
  by_contra hi
  have hb : Q ∈ frontier B :=
    ⟨closure_mono (t.domain_subset_backwardDomain c P W S C hP) hQ, hi⟩
  rcases t.mem_frontier_backwardDomain_imp_terminal_or_path_mem_singularSupport
    c A wall hclosed hheight hdir hb with ⟨j, _, hj⟩ | ⟨j, hj⟩
  · exact hendpoint _ hj
  · exact hregular j hj

/-- Nonclosed selected supports have no additional regular incidence boundary
when their germs at regular limits agree with their ambient walls. This applies
to exact simultaneous events, whose omitted wall indices must also persist. -/
theorem mem_interior_backwardDomain_of_locally_eq
    (hlocal : ∀ j x, x ∈ closure (P j) → x ∉ singularSupport A →
      ∀ᶠ y in 𝓝 x, y ∈ A (wall j) → y ∈ P j)
    {Q : V} (hQ : Q ∈ closure D) (hendpoint : ∀ i, Q ∉ A i)
    (hregular : ∀ j : Fin t.itinerary.val.length,
      t.path c Q (τ j.succ Q) ∉ singularSupport A) :
    Q ∈ interior (backwardDomain F b u (fun j => P (t.itinerary.val.get j))) := by
  have hambient := t.mem_interior_backwardDomain_of_notMem_singularSupport
    c P W S C A wall hclosed hP hheight hdir hQ hendpoint hregular
  have hnonneg := t.backwardTime_nonneg c P W S C hQ
  have hselected : ∀ᶠ Y in 𝓝 Q, ∀ j : Fin t.itinerary.val.length,
      backwardPoint F b u j.succ Y ∈ A (wall (t.itinerary.val.get j)) →
        backwardPoint F b u j.succ Y ∈ P (t.itinerary.val.get j) := by
    apply eventually_all.mpr
    intro j
    have hp := backwardPath_apply_parameter F b
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.history.val 0 j)) hnonneg j.succ
    simp only [Fin.snoc_castSucc] at hp
    have hclosure : backwardPoint F b u j.succ Q ∈ closure (P (t.itinerary.val.get j)) := by
      simpa only [path_def, Fin.snoc_castSucc, hp] using
        t.path_parameter_mem_closure c P W S C hQ j
    have hreg : backwardPoint F b u j.succ Q ∉ singularSupport A := by
      simpa only [path_def, Fin.snoc_castSucc, hp] using hregular j
    exact (backwardPoint F b u j.succ).continuous.continuousAt.eventually
      (hlocal _ _ hclosure hreg)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [mem_interior_iff_mem_nhds.mp hambient, hselected] with Y hY hsel
  exact (mem_backwardDomain ..).mpr fun j =>
    ⟨((mem_backwardDomain ..).mp hY j).1, hsel j ((mem_backwardDomain ..).mp hY j).2⟩

end Mei.CutoffDecoratedType
