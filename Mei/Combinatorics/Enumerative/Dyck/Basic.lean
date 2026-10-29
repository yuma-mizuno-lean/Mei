/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Data.Fintype.Fin

/-!
# Maximal Dyck paths

The maximal Dyck path of `(d₁, d₂) ∈ ℕ²` is the lattice path from `(0, 0)` to `(d₁, d₂)` by
horizontal and vertical unit steps which stays weakly below the diagonal and is closest to it.
We record a horizontal step as `DyckStep.U` and a vertical step as `DyckStep.D`. For `d₁ > 0`
the path consists of `d₁` blocks: the `i`-th horizontal step is followed by vertical steps up
to height `⌊i d₂ / d₁⌋`, the greatest height weakly below the diagonal. For `d₁ = 0` it is
vertical.

The path has `d₁` horizontal and `d₂` vertical steps. It is the Dyck word `(UD)^a` for
`(a, a)`, the vertical path `D^b` for `(0, b)` and the horizontal path `U^a` for `(a, 0)`.
-/

public section

open DyckStep Finset

namespace Mei

/-- The maximal Dyck path of `(d₁, d₂)`, with horizontal steps `U` and vertical steps `D`:
after its `i`-th horizontal step it rises to height `⌊i * d₂ / d₁⌋`. -/
def maximalDyckPath (d₁ d₂ : ℕ) : List DyckStep :=
  if d₁ = 0 then List.replicate d₂ D
  else (List.range d₁).flatMap fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D

/-- A path with no horizontal steps is vertical. -/
@[simp]
theorem maximalDyckPath_zero_left (d₂ : ℕ) : maximalDyckPath 0 d₂ = List.replicate d₂ D := by
  simp [maximalDyckPath]

/-- For `d₁ ≠ 0`, the path is the concatenation of its `d₁` horizontal blocks. -/
theorem maximalDyckPath_of_ne_zero {d₁ : ℕ} (d₂ : ℕ) (h : d₁ ≠ 0) :
    maximalDyckPath d₁ d₂ = (List.range d₁).flatMap
      fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D := by
  simp [maximalDyckPath, h]

/-- The first `n` horizontal blocks reach height `⌊n * d₂ / d₁⌋` after `n` horizontal steps. -/
private theorem counts_blocks (d₁ d₂ n : ℕ) :
    ((List.range n).flatMap fun i ↦
        U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D).count U = n ∧
      ((List.range n).flatMap fun i ↦
        U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D).count D = n * d₂ / d₁ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : n * d₂ / d₁ ≤ (n + 1) * d₂ / d₁ :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ n))
    simp only [List.range_succ, List.flatMap_append, List.count_append, ih.1, ih.2,
      List.flatMap_singleton, List.count_cons, List.count_replicate]
    constructor
    · simp
    · simp
      omega

/-- The path has `d₁` horizontal steps. -/
@[simp]
theorem count_U_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).count U = d₁ := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp [List.count_replicate]
  · rw [maximalDyckPath_of_ne_zero _ h]
    exact (counts_blocks d₁ d₂ d₁).1

/-- The path has `d₂` vertical steps. -/
@[simp]
theorem count_D_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).count D = d₂ := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h, (counts_blocks d₁ d₂ d₁).2,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h)]

/-- The path has `d₁ + d₂` steps. -/
@[simp]
theorem length_maximalDyckPath (d₁ d₂ : ℕ) : (maximalDyckPath d₁ d₂).length = d₁ + d₂ := by
  have hnot : (fun s : DyckStep ↦ decide (¬(s == U))) = (fun s ↦ s == D) := by
    funext s
    cases s <;> rfl
  rw [List.length_eq_countP_add_countP (fun s ↦ s == U), hnot,
    ← List.count_eq_countP, ← List.count_eq_countP, count_U_maximalDyckPath,
    count_D_maximalDyckPath]

/-- A path with no vertical steps is horizontal. -/
@[simp]
theorem maximalDyckPath_zero_right (d₁ : ℕ) : maximalDyckPath d₁ 0 = List.replicate d₁ U := by
  rcases eq_or_ne d₁ 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h]
    simp only [mul_zero, Nat.zero_div, Nat.sub_self, List.replicate_zero]
    rw [← List.map_eq_flatMap, List.map_const', List.length_range]

/-- The diagonal path alternates horizontal and vertical steps. -/
theorem maximalDyckPath_self (a : ℕ) :
    maximalDyckPath a a = (List.replicate a [U, D]).flatten := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [maximalDyckPath_of_ne_zero _ h]
    have hblock (i : ℕ) : (i + 1) * a / a - i * a / a = 1 := by
      rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h)]
      omega
    simp only [hblock, List.replicate_one]
    rw [List.flatMap, List.map_const', List.length_range]

namespace MaximalDyckPath

/-- The edges of the maximal Dyck path of `(d₁, d₂)`, indexed in traversal order. -/
abbrev Edge (d₁ d₂ : ℕ) := Fin (d₁ + d₂)

variable {d₁ d₂ : ℕ}

/-- The step taken along an edge of the maximal Dyck path. -/
def step (e : Edge d₁ d₂) : DyckStep :=
  (maximalDyckPath d₁ d₂)[e.val]'(by rw [length_maximalDyckPath]; exact e.isLt)

/-- An edge has the indexed step of the maximal Dyck path. -/
theorem step_def (e : Edge d₁ d₂) :
    step e = (maximalDyckPath d₁ d₂)[e.val]'(by rw [length_maximalDyckPath]; exact e.isLt) :=
  (rfl)

variable (d₁ d₂) in
/-- The vertical edges of the maximal Dyck path. -/
def verticalEdges : Finset (Edge d₁ d₂) := {e | step e = D}

variable (d₁ d₂) in
/-- The horizontal edges of the maximal Dyck path. -/
def horizontalEdges : Finset (Edge d₁ d₂) := {e | step e = U}

@[simp]
theorem mem_verticalEdges {e : Edge d₁ d₂} : e ∈ verticalEdges d₁ d₂ ↔ step e = D := by
  simp [verticalEdges]

@[simp]
theorem mem_horizontalEdges {e : Edge d₁ d₂} : e ∈ horizontalEdges d₁ d₂ ↔ step e = U := by
  simp [horizontalEdges]

/-- Counting edges of a given step type counts that step in the path. -/
private theorem card_step_eq (s : DyckStep) :
    #{e : Edge d₁ d₂ | step e = s} = (maximalDyckPath d₁ d₂).count s :=
  Fin.card_filter_univ_eq_vector_get_eq_count s
    ⟨maximalDyckPath d₁ d₂, length_maximalDyckPath d₁ d₂⟩

/-- The path has `d₂` vertical edges. -/
@[simp]
theorem card_verticalEdges : #(verticalEdges d₁ d₂) = d₂ := by
  rw [verticalEdges, card_step_eq, count_D_maximalDyckPath]

/-- The path has `d₁` horizontal edges. -/
@[simp]
theorem card_horizontalEdges : #(horizontalEdges d₁ d₂) = d₁ := by
  rw [horizontalEdges, card_step_eq, count_U_maximalDyckPath]

/-- Every edge is horizontal or vertical. -/
theorem mem_horizontalEdges_or_mem_verticalEdges (e : Edge d₁ d₂) :
    e ∈ horizontalEdges d₁ d₂ ∨ e ∈ verticalEdges d₁ d₂ := by
  simpa using (step e).dichotomy

/-- No edge is both horizontal and vertical. -/
theorem disjoint_horizontalEdges_verticalEdges :
    Disjoint (horizontalEdges d₁ d₂) (verticalEdges d₁ d₂) := by
  rw [Finset.disjoint_left]
  intro e hh hv
  rw [mem_horizontalEdges] at hh
  rw [mem_verticalEdges, hh] at hv
  exact DyckStep.noConfusion hv

/-- A horizontal edge is not vertical. -/
theorem notMem_verticalEdges_of_mem {e : Edge d₁ d₂} (he : e ∈ horizontalEdges d₁ d₂) :
    e ∉ verticalEdges d₁ d₂ :=
  Finset.disjoint_left.mp disjoint_horizontalEdges_verticalEdges he

/-- A vertical edge is not horizontal. -/
theorem notMem_horizontalEdges_of_mem {e : Edge d₁ d₂} (he : e ∈ verticalEdges d₁ d₂) :
    e ∉ horizontalEdges d₁ d₂ :=
  Finset.disjoint_right.mp disjoint_horizontalEdges_verticalEdges he

/-- The horizontal edges are the edges that are not vertical. -/
@[simp]
theorem compl_verticalEdges : (verticalEdges d₁ d₂)ᶜ = horizontalEdges d₁ d₂ := by
  ext e
  rw [mem_compl]
  rcases mem_horizontalEdges_or_mem_verticalEdges e with he | he
  · exact iff_of_true (notMem_verticalEdges_of_mem he) he
  · exact iff_of_false (not_not.mpr he) (notMem_horizontalEdges_of_mem he)

/-- The vertical edges are the edges that are not horizontal. -/
@[simp]
theorem compl_horizontalEdges : (horizontalEdges d₁ d₂)ᶜ = verticalEdges d₁ d₂ := by
  rw [← compl_verticalEdges, compl_compl]

end MaximalDyckPath

end Mei
