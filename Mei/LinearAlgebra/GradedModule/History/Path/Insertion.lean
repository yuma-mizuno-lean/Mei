/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path.Identity
public import Mei.LinearAlgebra.GradedModule.History.Path.Labels
public import Mei.Combinatorics.Quiver.Path.Insertion

/-!
# Segment labels after identity insertion

Repeating a degree at an identity arrow duplicates its segment label in backward
order. This connects the shared coefficient-history subdivision to geometric
insertion, where the normal and support tuples acquire one extra encounter.
-/

public section

namespace Quiver.Path

variable {Q A : Type*} [Quiver Q] {ι : Q → Type*} {a b : Q}

/-- Identity insertion repeats the segment direction, including for empty
prefixes or suffixes and for labels invisible in the developed space. -/
theorem Degrees.reverseVertexLabels_degreesRepeat (v : ∀ q, ι q → A)
    (p : Path a b) (e : b ⟶ b) (i : ι a) :
    ∀ {c : Q} (q : Path b c) (d : (p.comp q).Degrees ι),
      (fun j => reverseVertexLabels v i ((p.cons e).comp q) (degreesRepeat p q e i d)
        (Fin.cast (congrArg (fun n => n + 1) (length_insertLoop p q e)).symm j)) =
      (insertionIndex p q).succ.insertNth
        (reverseVertexLabels v i (p.comp q) d (insertionIndex p q))
        (reverseVertexLabels v i (p.comp q) d)
  | _, nil, d => by
    simp only [comp_nil, insertionIndex_nil]
    erw [degreesRepeat_nil, reverseVertexLabels_cons]
    rw [← reverseVertexLabels_zero v i p d]
    have hh := Fin.insertNth_succ_cons (0 : Fin (p.length + 1))
      (reverseVertexLabels v i p d 0) (reverseVertexLabels v i p d 0)
      (Fin.tail (reverseVertexLabels v i p d))
    -- The remaining differences are casts of the equal finite encounter counts.
    convert (by simpa only [Fin.insertNth_zero', Fin.cons_self_tail] using hh.symm) using 1 <;> rfl
  | _, cons q g, d => by
    simp only [comp_cons] at d ⊢
    obtain ⟨d, j⟩ := d
    simp only [degreesRepeat_cons, reverseVertexLabels_cons, insertionIndex_cons]
    have ih := reverseVertexLabels_degreesRepeat v p e i q d
    calc
      _ = Fin.cons (v _ j) (fun k => reverseVertexLabels v i ((p.cons e).comp q)
          (degreesRepeat p q e i d)
          (Fin.cast (congrArg (fun n => n + 1) (length_insertLoop p q e)).symm k)) := by
        funext k
        exact Fin.cases rfl (fun _ => rfl) k
      _ = Fin.cons (v _ j) ((insertionIndex p q).succ.insertNth
          (reverseVertexLabels v i (p.comp q) d (insertionIndex p q))
          (reverseVertexLabels v i (p.comp q) d)) :=
        congrArg (fun t : Fin ((p.comp q).length + 2) → A =>
          Fin.cons (α := fun _ => A) (v _ j) t) ih
      _ = _ := by erw [Fin.insertNth_succ_cons, Fin.cons_succ]

end Quiver.Path
