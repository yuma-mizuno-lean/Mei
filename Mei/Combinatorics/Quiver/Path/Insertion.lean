/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Combinatorics.Quiver.Path.Labels
public import Mei.Data.Fin.Insertion

/-!
# Inserting a loop between path blocks

The insertion position counts the arrows in the second block, since label
extraction reads paths backwards. Inserting a loop inserts precisely one arrow
label at that position. These formulas relate path concatenation to finite-tuple
insertion without identifying the vertices of the two blocks.
-/

public section

namespace Quiver.Path

variable {Q A : Type*} [Quiver Q] {a b : Q}

/-- The position between two blocks in the backward encounter tuple. -/
def insertionIndex (p : Path a b) : {c : Q} → (q : Path b c) → Fin ((p.comp q).length + 1)
  | _, nil => 0
  | _, cons q _ => (insertionIndex p q).succ

/-- An empty suffix places the extra encounter first in backward order. -/
@[simp]
theorem insertionIndex_nil (p : Path a b) : insertionIndex p nil = 0 := (rfl)

/-- A final arrow shifts the insertion position by one. -/
@[simp]
theorem insertionIndex_cons (p : Path a b) {c z : Q} (q : Path b c) (g : c ⟶ z) :
    insertionIndex p (q.cons g) = (insertionIndex p q).succ := (rfl)

/-- Inserting a loop adds one encounter. -/
theorem length_insertLoop (p : Path a b) {c : Q} (q : Path b c) (e : b ⟶ b) :
    ((p.cons e).comp q).length = (p.comp q).length + 1 := by
  simp only [length_comp, length_cons]
  omega

/-- Reading labels after insertion inserts the loop label at the block boundary. -/
theorem reverseArrowLabels_insertLoop (f : ∀ {u v : Q}, (u ⟶ v) → A)
    (p : Path a b) (e : b ⟶ b) : ∀ {c : Q} (q : Path b c),
    (fun j => ((p.cons e).comp q).reverseArrowLabels f
      (Fin.cast (length_insertLoop p q e).symm j)) =
        (insertionIndex p q).insertNth (f e) ((p.comp q).reverseArrowLabels f)
  | _, nil => by
    simp only [comp_nil, reverseArrowLabels_cons, insertionIndex]
    exact (Fin.insertNth_zero' (f e) (p.reverseArrowLabels f)).symm
  | _, cons q g => by
    simp only [comp_cons, reverseArrowLabels_cons, insertionIndex]
    calc
      _ = Fin.cons (f g) (fun j => ((p.cons e).comp q).reverseArrowLabels f
          (Fin.cast (length_insertLoop p q e).symm j)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      _ = Fin.cons (f g) ((insertionIndex p q).insertNth (f e)
          ((p.comp q).reverseArrowLabels f)) :=
        congrArg (fun t : Fin ((p.comp q).length + 1) → A =>
          Fin.cons (α := fun _ => A) (f g) t) (reverseArrowLabels_insertLoop f p e q)
      _ = _ := (Fin.insertNth_succ_cons (insertionIndex p q) (f e) (f g)
        ((p.comp q).reverseArrowLabels f)).symm

end Quiver.Path
