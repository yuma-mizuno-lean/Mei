/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path

/-!
# Vertex labels of a complete degree history

Assign values to the chamber degrees visited by a component history. The tuple
starts at the final component and ends at the prescribed incoming degree.
In particular, spatial directions can be extracted without identifying the
different chambers' degree types or coefficient modules.
-/

public section

namespace Quiver.Path.Degrees

variable {Q A B : Type*} [Quiver Q] {ι : Q → Type*} {a : Q}

/-- Labels of every segment of a complete history in backward order, including
the incoming segment. Repeated or spatially equal degrees remain separate. -/
def reverseVertexLabels (v : ∀ q, ι q → A) (i₀ : ι a) :
    {b : Q} → (p : Path a b) → p.Degrees ι → Fin (p.length + 1) → A
  | _, nil, _ => fun _ => v a i₀
  | _, @cons _ _ _ _ c p _, d =>
      Fin.cons (v c d.2) (reverseVertexLabels v i₀ p d.1)

/-- An empty history retains the incoming label. -/
@[simp]
theorem reverseVertexLabels_nil (v : ∀ q, ι q → A) (i₀ : ι a)
    (d : (nil : Path a a).Degrees ι) :
    reverseVertexLabels v i₀ nil d = fun _ => v a i₀ := (rfl)

/-- The next component is prepended to the backward segment labels. -/
@[simp]
theorem reverseVertexLabels_cons (v : ∀ q, ι q → A) (i₀ : ι a)
    {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    reverseVertexLabels v i₀ (p.cons e) (d, i) =
      Fin.cons (v c i) (reverseVertexLabels v i₀ p d) := (rfl)

/-- The label of the final segment is that of the last selected degree. -/
@[simp]
theorem reverseVertexLabels_cons_zero (v : ∀ q, ι q → A) (i₀ : ι a)
    {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι) (i : ι c) :
    reverseVertexLabels v i₀ (p.cons e) (d, i) (0 : Fin (p.length + 1 + 1)) = v c i :=
  Fin.cons_zero ..

/-- The labels of earlier segments are those of the shorter history. -/
@[simp]
theorem reverseVertexLabels_cons_succ (v : ∀ q, ι q → A) (i₀ : ι a)
    {b c : Q} (p : Path a b) (e : b ⟶ c) (d : p.Degrees ι) (i : ι c)
    (j : Fin (p.length + 1)) :
    reverseVertexLabels v i₀ (p.cons e) (d, i) j.succ = reverseVertexLabels v i₀ p d j :=
  Fin.cons_succ ..

/-- The endpoint label belongs to the terminal chamber degree. -/
@[simp]
theorem reverseVertexLabels_zero (v : ∀ q, ι q → A) (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      reverseVertexLabels v i₀ p d 0 = v b (terminalDegree i₀ p d)
  | _, nil, _ => rfl
  | _, cons _ _, _ => Fin.cons_zero ..

/-- The entire incoming history ends at its original incoming label. -/
@[simp]
theorem reverseVertexLabels_last (v : ∀ q, ι q → A) (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      reverseVertexLabels v i₀ p d (Fin.last p.length) = v a i₀
  | _, nil, _ => rfl
  | _, cons p _, d => by
    exact (Fin.cons_succ _ _ (Fin.last p.length)).trans
      (reverseVertexLabels_last v i₀ p d.1)

/-- A map on labels commutes with extracting all segment directions. -/
theorem reverseVertexLabels_comp (v : ∀ q, ι q → A) (g : A → B) (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      reverseVertexLabels (fun q i => g (v q i)) i₀ p d =
        g ∘ reverseVertexLabels v i₀ p d
  | _, nil, _ => rfl
  | _, cons p e, d => by
    funext j
    exact Fin.cases rfl (fun k => congrFun (reverseVertexLabels_comp v g i₀ p d.1) k) j

end Quiver.Path.Degrees
