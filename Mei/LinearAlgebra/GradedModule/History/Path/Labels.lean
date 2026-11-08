/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path.Identity
public import Mei.Combinatorics.Quiver.Path.Erasure

/-!
# Vertex labels of a complete degree history

Assign values to the chamber degrees visited by a component history. The tuple
starts at the final component and ends at the prescribed incoming degree.
In particular, spatial directions can be extracted without identifying the
different chambers' degree types or coefficient modules. Erasing a loop
that preserves its adjacent degree retains the labels at all remaining
parameters, while the erased arrow's two segment labels agree.
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

/-- Regrading a history preserves all its segment labels when the vertex labels
intertwine the degree maps, including the incoming segment. -/
@[simp]
theorem reverseVertexLabels_map {κ : Q → Type*} (σ : ∀ q, ι q → κ q)
    (v : ∀ q, ι q → A) (w : ∀ q, κ q → A) (hv : ∀ q d, w q (σ q d) = v q d)
    (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      reverseVertexLabels w (σ a i₀) p (map σ p d) = reverseVertexLabels v i₀ p d
  | _, nil, _ => by simp [hv]
  | _, cons p e, d => by
    obtain ⟨d, i⟩ := d
    rw [map_cons, reverseVertexLabels_cons, reverseVertexLabels_cons]
    exact congrArg₂ Fin.cons (hv _ _) (reverseVertexLabels_map σ v w hv i₀ p d)

end Quiver.Path.Degrees

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {ι : Q → Type*} {a b : Q}
  (p : Path a b) (e : b ⟶ b)

variable {A : Type*} (v : ∀ q, ι q → A) (i₀ : ι a)

/-- At a retained encounter the outgoing segment keeps its label. This does
not require the labels adjacent to the omitted loop to agree. -/
theorem reverseVertexLabels_loopErasure_castSucc : ∀ {c : Q} (q : Path b c)
    (d : ((p.cons e).comp q).Degrees ι) (j : Fin (p.comp q).length),
    Degrees.reverseVertexLabels v i₀ (p.comp q) (degreesErase p q e d) j.castSucc =
      Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d
        (loopErasureArrow p e q j).castSucc
  | _, nil, d, j => by
    rw [loopErasureArrow_nil p e j]
    obtain ⟨d, i⟩ := d
    simp only [comp_nil, degreesErase_nil (ι := ι)]
    rw [Degrees.reverseVertexLabels_cons v i₀ p e d i]
    exact (Fin.cons_succ (α := fun _ => A) (v b i)
      (Degrees.reverseVertexLabels v i₀ p d) j.castSucc).symm
  | _, cons q g, d, j => by
    obtain ⟨d, i⟩ := d
    simp only [comp_cons, degreesErase_cons (ι := ι)]
    rw [Degrees.reverseVertexLabels_cons v i₀ (p.comp q) g _ i,
      Degrees.reverseVertexLabels_cons v i₀ ((p.cons e).comp q) g d i]
    cases j using Fin.cases with
    | zero =>
      rw [loopErasureArrow_cons_zero p e q g]
      exact (Fin.cons_zero (α := fun _ => A) _ _).trans (Fin.cons_zero (α := fun _ => A) _ _).symm
    | succ j =>
      rw [loopErasureArrow_cons_succ p e q g j]
      exact (Fin.cons_succ (α := fun _ => A) _ _ j.castSucc).trans
        ((reverseVertexLabels_loopErasure_castSucc q d j).trans
          (Fin.cons_succ (α := fun _ => A) _ _ (loopErasureArrow p e q j).castSucc).symm)

/-- Equal degrees at the erased loop preserve segment labels at every retained
parameter, including the endpoint. -/
theorem reverseVertexLabels_loopErasureParameter : ∀ {c : Q} (q : Path b c)
    (d : ((p.cons e).comp q).Degrees ι)
    (_ : (degreesComp (ι := ι) (p.cons e) q d).1.2 =
      Degrees.terminalDegree i₀ p (degreesComp (ι := ι) (p.cons e) q d).1.1)
    (j : Fin ((p.comp q).length + 1)),
    Degrees.reverseVertexLabels v i₀ (p.comp q) (degreesErase p q e d) j =
      Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d
        (loopErasureParameter p e q j)
  | _, nil, d, hd, j => by
    rw [degreesComp_nil (ι := ι) (p.cons e) d] at hd
    obtain ⟨d, i⟩ := d
    simp only [comp_nil, degreesErase_nil (ι := ι)]
    rw [Degrees.reverseVertexLabels_cons v i₀ p e d i]
    cases j using Fin.cases with
    | zero =>
      rw [loopErasureParameter_zero p e nil]
      exact (Degrees.reverseVertexLabels_zero v i₀ p d).trans
        ((congrArg (v b) hd.symm).trans (Fin.cons_zero (α := fun _ => A) _ _).symm)
    | succ j =>
      rw [loopErasureParameter_succ p e nil j, loopErasureArrow_nil p e j]
      exact (Fin.cons_succ (α := fun _ => A) _ _ j.succ).symm
  | _, cons q g, d, hd, j => by
    obtain ⟨d, i⟩ := d
    rw [degreesComp_cons (ι := ι)] at hd
    simp only [comp_cons, degreesErase_cons (ι := ι)]
    rw [Degrees.reverseVertexLabels_cons v i₀ (p.comp q) g _ i,
      Degrees.reverseVertexLabels_cons v i₀ ((p.cons e).comp q) g d i]
    cases j using Fin.cases with
    | zero =>
      rw [loopErasureParameter_zero p e (q.cons g)]
      exact (Fin.cons_zero (α := fun _ => A) _ _).trans (Fin.cons_zero (α := fun _ => A) _ _).symm
    | succ j =>
      exact (Fin.cons_succ (α := fun _ => A) _ _ j).trans
        ((reverseVertexLabels_loopErasureParameter q d hd j).trans
          ((Fin.cons_succ (α := fun _ => A) _ _ (loopErasureParameter p e q j)).symm.trans
            (congrArg (Fin.cons (α := fun _ => A) (v _ i)
              (Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d))
                (loopErasureParameter_cons_succ p e q g j).symm)))

/-- Equal adjacent degrees make the omitted encounter spatially unbent. -/
theorem reverseVertexLabels_loopIndex_eq : ∀ {c : Q} (q : Path b c)
    (d : ((p.cons e).comp q).Degrees ι)
    (_ : (degreesComp (ι := ι) (p.cons e) q d).1.2 =
      Degrees.terminalDegree i₀ p (degreesComp (ι := ι) (p.cons e) q d).1.1),
    Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d (loopIndex p e q).succ =
      Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d (loopIndex p e q).castSucc
  | _, nil, d, hd => by
    rw [degreesComp_nil (ι := ι) (p.cons e) d] at hd
    obtain ⟨d, i⟩ := d
    rw [loopIndex_nil p e]
    simp only [comp_nil]
    rw [Degrees.reverseVertexLabels_cons v i₀ p e d i]
    exact (Fin.cons_succ (α := fun _ => A) _ _ (0 : Fin (p.length + 1))).trans
      ((Degrees.reverseVertexLabels_zero v i₀ p d).trans
        ((congrArg (v b) hd.symm).trans (Fin.cons_zero (α := fun _ => A) _ _).symm))
  | _, cons q g, d, hd => by
    obtain ⟨d, i⟩ := d
    rw [degreesComp_cons (ι := ι)] at hd
    rw [loopIndex_cons p e q g]
    simp only [comp_cons]
    rw [Degrees.reverseVertexLabels_cons v i₀ ((p.cons e).comp q) g d i]
    exact (Fin.cons_succ (α := fun _ => A) _ _ (loopIndex p e q).succ).trans
      ((reverseVertexLabels_loopIndex_eq q d hd).trans
        (Fin.cons_succ (α := fun _ => A) _ _ (loopIndex p e q).castSucc).symm)

end Quiver.Path
