/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Combinatorics.Quiver.Path
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Arrow labels in backward path order

Extract a tuple of labels from a quiver path, with its last arrow at index zero.
This order lets backward reconstruction use the same encounter inventory as
forward composition, including repeated arrows.
-/

public section

namespace Quiver.Path

variable {Q A B : Type*} [Quiver Q] {a : Q}

/-- The arrow labels of a path, starting with its last arrow. -/
def reverseArrowLabels (f : ∀ {b c : Q}, (b ⟶ c) → A) :
    {b : Q} → (p : Path a b) → Fin p.length → A
  | _, nil => Fin.elim0
  | _, cons p e => Fin.cons (f e) (p.reverseArrowLabels f)

/-- The empty path has no arrow labels. -/
@[simp]
theorem reverseArrowLabels_nil (f : ∀ {b c : Q}, (b ⟶ c) → A) :
    (nil : Path a a).reverseArrowLabels f = Fin.elim0 := (rfl)

/-- Appending an arrow places its label first in backward order. -/
@[simp]
theorem reverseArrowLabels_cons (f : ∀ {b c : Q}, (b ⟶ c) → A)
    {b c : Q} (p : Path a b) (e : b ⟶ c) :
    (p.cons e).reverseArrowLabels f = Fin.cons (f e) (p.reverseArrowLabels f) := (rfl)

/-- Applying a function to labels commutes with extracting the tuple. -/
theorem reverseArrowLabels_comp (f : ∀ {b c : Q}, (b ⟶ c) → A) (g : A → B) :
    ∀ {b : Q} (p : Path a b),
      p.reverseArrowLabels (fun e => g (f e)) = g ∘ p.reverseArrowLabels f
  | _, nil => funext fun j => j.elim0
  | _, cons p e => by
    funext j
    exact Fin.cases rfl (fun k => congrFun (reverseArrowLabels_comp f g p) k) j

/-- Every tuple entry inherits a property of all arrow labels. -/
theorem reverseArrowLabels_forall (f : ∀ {b c : Q}, (b ⟶ c) → A)
    (P : A → Prop) (hf : ∀ {b c : Q} (e : b ⟶ c), P (f e)) :
    ∀ {b : Q} (p : Path a b) (j : Fin p.length), P (p.reverseArrowLabels f j)
  | _, nil, j => j.elim0
  | _, cons p e, j => Fin.cases (hf e) (reverseArrowLabels_forall f P hf p) j

end Quiver.Path
