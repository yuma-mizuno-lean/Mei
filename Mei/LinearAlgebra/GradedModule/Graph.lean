/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import Mei.Algebra.PositiveDegrees.Graph
public import Mei.Algebra.PositiveDegrees.Grading

/-!
# Gradings on a graph of degrees

An internal grading indexed by `ι` can be indexed by the graph `(f i, i)` in
`κ × ι`. Its pieces vanish off the graph, and projection to the second coordinate
recovers the original homogeneous components. Retaining that coordinate allows
`f` to have a kernel without merging any homogeneous pieces.

The decomposition uses `DirectSum.IsInternal.iSup_fiber`, and the component
comparison uses `DirectSum.map_decompose_shift`.
-/

public section

noncomputable section

namespace Mei

variable {R M ι κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M) (f : ι → κ)

/-- Reindex a family of homogeneous pieces along the graph `i ↦ (f i, i)`,
with zero pieces away from that graph. -/
def graphGrading (p : κ × ι) : Submodule R M := by
  classical
  exact if p.1 = f p.2 then ℳ p.2 else ⊥

/-- The graph grading retains precisely the original piece on the graph. -/
@[simp]
theorem graphGrading_apply (i : ι) : graphGrading ℳ f (f i, i) = ℳ i := by
  simp [graphGrading]

/-- Every degree off the graph has zero homogeneous piece. -/
@[simp]
theorem graphGrading_eq_bot {p : κ × ι} (hp : p.1 ≠ f p.2) :
    graphGrading ℳ f p = ⊥ := by
  simp [graphGrading, hp]

/-- At any index the graph piece lies in its original second-coordinate piece. -/
theorem graphGrading_le (p : κ × ι) : graphGrading ℳ f p ≤ ℳ p.2 := by
  classical
  simp only [graphGrading]
  split_ifs <;> simp

private theorem graphGrading_eq_iSup (p : κ × ι) :
    graphGrading ℳ f p = ⨆ i, ⨆ (_ : (f i, i) = p), ℳ i := by
  classical
  apply le_antisymm
  · by_cases hp : p.1 = f p.2
    · have he : (f p.2, p.2) = p := Prod.ext hp.symm rfl
      rw [← he, graphGrading_apply]
      exact le_iSup_of_le p.2 (le_iSup_of_le rfl le_rfl)
    · rw [graphGrading_eq_bot ℳ f hp]
      exact bot_le
  · refine iSup_le fun i => iSup_le fun hi => ?_
    subst p
    simp

section Decomposition

variable [DecidableEq ι] [DecidableEq κ] [DirectSum.Decomposition ℳ]

/-- Graph reindexing preserves the internal direct-sum decomposition. -/
instance instDecompositionGraphGrading : DirectSum.Decomposition (graphGrading ℳ f) :=
  (show DirectSum.IsInternal (graphGrading ℳ f) from by
    have h := (DirectSum.Decomposition.isInternal ℳ).iSup_fiber (fun i => (f i, i))
    simpa only [← graphGrading_eq_iSup] using h).chooseDecomposition

/-- Graph reindexing preserves each homogeneous component at its graph degree. -/
@[simp]
theorem decompose_graphGrading (x : M) (i : ι) :
    (DirectSum.decompose (graphGrading ℳ f) x (f i, i) : M) =
      (DirectSum.decompose ℳ x i : M) := by
  exact (DirectSum.map_decompose_shift ℳ (graphGrading ℳ f) (AddMonoidHom.id M)
    (fun i => (f i, i)) (fun _ _ h => congrArg Prod.snd h)
    (fun i x hx => by simpa using hx) i x).symm

end Decomposition

section Positive

variable {N K : Type*} [AddCommMonoid N] [AddCommMonoid K]
  (ℒ : N → Submodule R M) (g : N →+ K) (d : PositiveDegrees N)

/-- A positive grading remains positive on graph degree data. -/
instance instIsPositiveGradingGraphGrading [IsPositiveGrading d ℒ] :
    IsPositiveGrading (d.graph g) (graphGrading ℒ g) where
  eq_bot := by
    rintro ⟨m, n⟩ hn
    by_cases hm : m = g n
    · subst m
      rw [graphGrading_apply]
      apply IsPositiveGrading.eq_bot (d := d)
      rcases hn with hn | hn
      · exact Or.inl (fun h => hn ((PositiveDegrees.mem_graph_monoid d g _ _).mpr ⟨h, rfl⟩))
      · exact Or.inr (congrArg Prod.snd hn)
    · exact graphGrading_eq_bot ℒ g hm

/-- Reindexing on a graph leaves every degree submodule unchanged, without
requiring an internal decomposition or a Lie-compatible grading. -/
@[simp]
theorem degreeSubmodule_graphGrading (k : ℕ) :
    (d.graph g).degreeSubmodule (graphGrading ℒ g) k = d.degreeSubmodule ℒ k := by
  apply le_antisymm
  · rw [PositiveDegrees.degreeSubmodule_def]
    refine iSup_le fun ⟨⟨m, n⟩, hn⟩ => ?_
    exact (graphGrading_le ℒ g (m, n)).trans
      (d.le_degreeSubmodule ℒ (by simpa using hn))
  · rw [PositiveDegrees.degreeSubmodule_def]
    refine iSup_le fun n => ?_
    rw [← graphGrading_apply ℒ g n]
    exact (d.graph g).le_degreeSubmodule (graphGrading ℒ g) (by simpa using n.property)

end Positive

end Mei
