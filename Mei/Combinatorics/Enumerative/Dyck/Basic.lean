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
When `0 < d₁ + d₂`, every prefix with `x` horizontal and `y` vertical steps satisfies
`d₁ y ≤ d₂ x < d₁ y + d₁ + d₂`, so its lattice distance below the diagonal is less than
`d₁ + d₂`.
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

/-- The first `m` horizontal blocks of the path. -/
private def blocks (d₁ d₂ m : ℕ) : List DyckStep :=
  (List.range m).flatMap fun i ↦ U :: List.replicate ((i + 1) * d₂ / d₁ - i * d₂ / d₁) D

private theorem blocks_succ (d₁ d₂ m : ℕ) :
    blocks d₁ d₂ (m + 1) =
      blocks d₁ d₂ m ++ U :: List.replicate ((m + 1) * d₂ / d₁ - m * d₂ / d₁) D := by
  simp [blocks, List.range_succ, List.flatMap_append]

/-- The first `n` horizontal blocks reach height `⌊n * d₂ / d₁⌋` after `n` horizontal steps. -/
private theorem counts_blocks (d₁ d₂ n : ℕ) :
    (blocks d₁ d₂ n).count U = n ∧ (blocks d₁ d₂ n).count D = n * d₂ / d₁ := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    have hle : n * d₂ / d₁ ≤ (n + 1) * d₂ / d₁ :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ n))
    simp only [blocks_succ, List.count_append, ih.1, ih.2, List.count_cons, List.count_replicate]
    constructor
    · simp
    · simp
      omega

/-- Every prefix of the first `m` blocks lies weakly below the diagonal and less than `d₁ + d₂`
below it, in the lattice distance `d₂ x - d₁ y`. -/
private theorem count_take_blocks {d₁ : ℕ} (d₂ : ℕ) (hd₁ : 0 < d₁) (m k : ℕ) :
    d₁ * ((blocks d₁ d₂ m).take k).count D ≤ d₂ * ((blocks d₁ d₂ m).take k).count U ∧
      d₂ * ((blocks d₁ d₂ m).take k).count U <
        d₁ * ((blocks d₁ d₂ m).take k).count D + (d₁ + d₂) := by
  induction m generalizing k with
  | zero => simpa [blocks] using Nat.add_pos_left hd₁ d₂
  | succ m ih =>
    rw [blocks_succ, List.take_append]
    by_cases hk : k ≤ (blocks d₁ d₂ m).length
    · rw [Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
      exact ih k
    obtain ⟨j, hj⟩ : ∃ j, k - (blocks d₁ d₂ m).length = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      (by omega)).symm⟩
    rw [List.take_of_length_le (by omega), hj, List.take_succ_cons, List.take_replicate]
    simp only [List.count_append, (counts_blocks d₁ d₂ m).1, (counts_blocks d₁ d₂ m).2,
      List.count_cons, List.count_replicate]
    simp only [beq_self_eq_true, ↓reduceIte, reduceCtorEq, beq_iff_eq]
    set a := m * d₂ / d₁
    set b := (m + 1) * d₂ / d₁
    have hab : a ≤ b := Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ m))
    have hb : b * d₁ ≤ (m + 1) * d₂ := Nat.div_mul_le_self _ _
    have ha : m * d₂ < a * d₁ + d₁ := Nat.lt_div_mul_add hd₁
    have hi : a + min j (b - a) ≤ b := by omega
    have hi' : d₁ * (a + min j (b - a)) ≤ d₁ * b := Nat.mul_le_mul_left _ hi
    have ha' : d₁ * a ≤ d₁ * (a + min j (b - a)) := Nat.mul_le_mul_left _ (by omega)
    constructor <;> nlinarith

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
  · rw [maximalDyckPath_of_ne_zero _ h, ← blocks, (counts_blocks d₁ d₂ d₁).2,
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

/-- **The path stays near the diagonal.** With `x` horizontal and `y` vertical steps in a prefix,
`d₁ y ≤ d₂ x < d₁ y + d₁ + d₂`: the prefix lies weakly below the diagonal, at lattice distance
less than `d₁ + d₂`. -/
theorem mul_count_take_maximalDyckPath_le_and_lt {d₁ d₂ : ℕ} (hd : 0 < d₁ + d₂) (k : ℕ) :
    d₁ * ((maximalDyckPath d₁ d₂).take k).count D ≤
        d₂ * ((maximalDyckPath d₁ d₂).take k).count U ∧
      d₂ * ((maximalDyckPath d₁ d₂).take k).count U <
        d₁ * ((maximalDyckPath d₁ d₂).take k).count D + (d₁ + d₂) := by
  rcases Nat.eq_zero_or_pos d₁ with rfl | hd₁
  · simpa [List.take_replicate, List.count_replicate] using hd
  · rw [maximalDyckPath_of_ne_zero _ hd₁.ne', ← blocks]
    exact count_take_blocks d₂ hd₁ d₁ k

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
  (List.Vector.count_toList s
    ⟨maximalDyckPath d₁ d₂, length_maximalDyckPath d₁ d₂⟩).symm

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

/-- Every non-vertical edge is horizontal. -/
theorem mem_horizontalEdges_of_notMem_verticalEdges {e : Edge d₁ d₂}
    (he : e ∉ verticalEdges d₁ d₂) : e ∈ horizontalEdges d₁ d₂ := by
  rwa [← compl_verticalEdges, mem_compl]

/-- The vertical edges are the edges that are not horizontal. -/
@[simp]
theorem compl_horizontalEdges : (horizontalEdges d₁ d₂)ᶜ = verticalEdges d₁ d₂ := by
  rw [← compl_verticalEdges, compl_compl]

end MaximalDyckPath

end Mei
