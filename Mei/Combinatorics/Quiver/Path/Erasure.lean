/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Combinatorics.Quiver.Path.Labels
public import Mathlib.Order.Fin.Tuple

/-!
# Indices after erasing a loop in a path

Erasing a loop between two path blocks retains the order of all other arrows.
The corresponding parameter indices retain the endpoint at index zero and omit
the erased encounter. These maps relate backward encounter tuples without
identifying the vertices or arrow types of the two blocks.
-/

public section

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {a b : Q} (p : Path a b) (e : b ⟶ b)

/-- Position of a loop between two blocks, in backward encounter order. -/
def loopIndex : {c : Q} → (q : Path b c) → Fin (((p.cons e).comp q).length)
  | _, nil => (0 : Fin (p.length + 1))
  | _, cons q _ => (loopIndex q).succ

/-- The order-preserving inclusion of the arrows remaining after loop erasure. -/
def loopErasureArrow : {c : Q} → (q : Path b c) →
    Fin (p.comp q).length → Fin (((p.cons e).comp q).length)
  | _, nil => Fin.succ
  | _, cons q _ => Fin.cases (0 : Fin ((((p.cons e).comp q).length) + 1))
      (fun j => (loopErasureArrow q j).succ)

/-- Retained parameter indices: the endpoint stays at zero, and the parameter
of each retained encounter is the successor of its arrow index. -/
def loopErasureParameter {c : Q} (q : Path b c) :
    Fin ((p.comp q).length + 1) → Fin ((((p.cons e).comp q).length) + 1) :=
  Fin.cases 0 (fun j => (loopErasureArrow p e q j).succ)

@[simp]
theorem loopErasureParameter_zero {c : Q} (q : Path b c) :
    loopErasureParameter p e q 0 = 0 := (rfl)

@[simp]
theorem loopErasureParameter_succ {c : Q} (q : Path b c)
    (j : Fin (p.comp q).length) :
    loopErasureParameter p e q j.succ = (loopErasureArrow p e q j).succ := (rfl)

/-- The selected loop is last when the suffix is empty. -/
@[simp]
theorem loopIndex_nil : loopIndex p e nil = (0 : Fin (p.length + 1)) := (rfl)

/-- Appending an arrow shifts the loop's backward index. -/
@[simp]
theorem loopIndex_cons {c d : Q} (q : Path b c) (g : c ⟶ d) :
    loopIndex p e (q.cons g) = (loopIndex p e q).succ := (rfl)

/-- Erasing a final loop shifts every earlier arrow index. -/
@[simp]
theorem loopErasureArrow_nil (j : Fin p.length) :
    loopErasureArrow p e nil j = j.succ := (rfl)

/-- A retained final arrow stays at index zero. -/
@[simp]
theorem loopErasureArrow_cons_zero {c d : Q} (q : Path b c) (g : c ⟶ d) :
    loopErasureArrow p e (q.cons g) (0 : Fin ((p.comp q).length + 1)) =
      (0 : Fin ((((p.cons e).comp q).length) + 1)) := (rfl)

/-- Earlier retained arrows shift together when a final arrow is appended. -/
@[simp]
theorem loopErasureArrow_cons_succ {c d : Q} (q : Path b c) (g : c ⟶ d)
    (j : Fin (p.comp q).length) :
    loopErasureArrow p e (q.cons g) j.succ = (loopErasureArrow p e q j).succ := (rfl)

/-- Earlier parameters shift together when a final arrow is appended. -/
@[simp]
theorem loopErasureParameter_cons_succ {c d : Q} (q : Path b c) (g : c ⟶ d)
    (j : Fin ((p.comp q).length + 1)) :
    loopErasureParameter p e (q.cons g) j.succ =
      (loopErasureParameter p e q j).succ := by
  cases j using Fin.cases <;> rfl

/-- The retained arrows remain strictly ordered. -/
theorem strictMono_loopErasureArrow : ∀ {c : Q} (q : Path b c),
    StrictMono (loopErasureArrow p e q)
  | _, nil => Fin.strictMono_succ
  | _, @cons _ _ _ _ _ q _ => by
    -- `Fin.cases` with constant first value is `Fin.cons` by definitional unfolding.
    change StrictMono (Fin.cons (0 : Fin (((p.cons e).comp q).length + 1))
      (Fin.succ ∘ loopErasureArrow p e q))
    exact Fin.strictMono_cons.2
      ⟨fun j => Fin.succ_pos (loopErasureArrow p e q j),
        Fin.strictMono_succ.comp (strictMono_loopErasureArrow q)⟩

/-- Parameter inclusion preserves the strict order, including the endpoint. -/
theorem strictMono_loopErasureParameter {c : Q} (q : Path b c) :
    StrictMono (loopErasureParameter p e q) :=
  Fin.strictMono_cons.2
    ⟨fun j => Fin.succ_pos (loopErasureArrow p e q j),
      Fin.strictMono_succ.comp (strictMono_loopErasureArrow p e q)⟩

/-- Exactly the selected loop is omitted from the encounter record. -/
theorem eq_loopIndex_or_exists_loopErasureArrow : ∀ {c : Q} (q : Path b c)
    (j : Fin (((p.cons e).comp q).length)),
    j = loopIndex p e q ∨ ∃ i, loopErasureArrow p e q i = j
  | _, nil, j => by
    cases j using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, rfl⟩
  | _, cons q f, j => by
    cases j using Fin.cases with
    | zero => exact Or.inr ⟨(0 : Fin ((p.comp q).length + 1)), rfl⟩
    | succ j =>
      rcases eq_loopIndex_or_exists_loopErasureArrow q j with h | ⟨i, rfl⟩
      · exact Or.inl (congrArg Fin.succ h)
      · exact Or.inr ⟨i.succ, rfl⟩

/-- No retained arrow has the erased loop's index. -/
theorem loopErasureArrow_ne_loopIndex : ∀ {c : Q} (q : Path b c)
    (j : Fin (p.comp q).length), loopErasureArrow p e q j ≠ loopIndex p e q
  | _, nil, j => Fin.succ_ne_zero j
  | _, cons q _, j => by
    cases j using Fin.cases with
    | zero => exact ne_of_lt (Fin.succ_pos _)
    | succ j => exact fun h => loopErasureArrow_ne_loopIndex q j (Fin.succ_injective _ h)

/-- The erased encounter time is absent from the retained parameter list. -/
theorem loopErasureParameter_ne_loopIndex_succ {c : Q} (q : Path b c)
    (j : Fin ((p.comp q).length + 1)) :
    loopErasureParameter p e q j ≠ (loopIndex p e q).succ := by
  cases j using Fin.cases with
  | zero =>
    rw [loopErasureParameter_zero]
    exact ne_of_lt (Fin.succ_pos _)
  | succ j =>
    rw [loopErasureParameter_succ]
    exact fun h => loopErasureArrow_ne_loopIndex p e q j (Fin.succ_injective _ h)

/-- Erasure retains every other arrow's label in its original order. -/
theorem reverseArrowLabels_loopErasure {A : Type*}
    (f : ∀ {u v : Q}, (u ⟶ v) → A) : ∀ {c : Q} (q : Path b c)
    (j : Fin (p.comp q).length),
    (p.comp q).reverseArrowLabels f j =
      ((p.cons e).comp q).reverseArrowLabels f (loopErasureArrow p e q j)
  | _, nil, j => by
    simpa only [comp_nil, loopErasureArrow, reverseArrowLabels_cons] using
      (Fin.cons_succ (α := fun _ => A) (f e) (p.reverseArrowLabels f) j).symm
  | _, cons q _, j => by
    cases j using Fin.cases with
    | zero => simp [comp_cons, reverseArrowLabels_cons, loopErasureArrow]
    | succ j =>
      simpa [comp_cons, reverseArrowLabels_cons, loopErasureArrow] using
        reverseArrowLabels_loopErasure f q j

end Quiver.Path
