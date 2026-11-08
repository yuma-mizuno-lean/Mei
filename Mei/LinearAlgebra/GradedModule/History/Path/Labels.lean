/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.LinearAlgebra.GradedModule.History.Path.Erasure
public import Mei.Combinatorics.Quiver.Path.Erasure
public import Mei.Combinatorics.Quiver.Path.Labels

/-!
# Vertex labels of a complete degree history

Assign values to the chamber degrees visited by a component history. The tuple
starts at the final component and ends at the prescribed incoming degree.
In particular, spatial directions can be extracted without identifying the
different chambers' degree types or coefficient modules. Erasing a loop
that preserves its adjacent degree retains the labels at all remaining
parameters, while the erased arrow's two segment labels agree. For a uniformly graded
semimodule, the reverse labels identify a path history with a finite sequence history.
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

/-- Extracting segment labels commutes with combining two labellings pointwise. -/
theorem reverseVertexLabels_map₂ {C : Type*} (v : ∀ q, ι q → A)
    (w : ∀ q, ι q → B) (f : A → B → C) (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      reverseVertexLabels (fun q i => f (v q i) (w q i)) i₀ p d =
        fun j => f (reverseVertexLabels v i₀ p d j) (reverseVertexLabels w i₀ p d j)
  | _, nil, _ => by simp only [reverseVertexLabels_nil]
  | _, cons p e, d => by
    obtain ⟨d, i⟩ := d
    rw [reverseVertexLabels_cons, reverseVertexLabels_cons, reverseVertexLabels_cons]
    funext j
    exact Fin.cases rfl (fun j => congrFun (reverseVertexLabels_map₂ v w f i₀ p d) j) j

/-- A relation between an arrow label and its adjacent segment labels holds
throughout the backward history if it holds at every arrow and degree pair. -/
theorem reverseLabels_forall (f : ∀ {b c : Q}, (b ⟶ c) → A)
    (v : ∀ q, ι q → B) (P : A → B → B → Prop)
    (hf : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), P (f e) (v c j) (v b i))
    (i₀ : ι a) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι) (j : Fin p.length),
      P (p.reverseArrowLabels f j) (reverseVertexLabels v i₀ p d j.castSucc)
        (reverseVertexLabels v i₀ p d j.succ)
  | _, nil, _, j => j.elim0
  | _, cons p e, d, j => by
    obtain ⟨d, i⟩ := d
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Path.length_cons, Fin.castSucc_zero, reverseVertexLabels_cons,
        Path.reverseArrowLabels_cons,
        Fin.cons_zero, Fin.cons_succ, reverseVertexLabels_zero] using
        hf e (terminalDegree i₀ p d) i
    · simpa only [Path.length_cons, Fin.castSucc_succ, reverseVertexLabels_cons,
        Path.reverseArrowLabels_cons,
        Fin.cons_succ] using reverseLabels_forall f v P hf i₀ p d j

end Quiver.Path.Degrees

namespace Quiver.Path

section Erasure

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
    obtain ⟨d, i⟩ := d
    simp only [comp_nil, degreesErase_nil]
    rw [loopErasureArrow_nil p e j]
    exact (Degrees.reverseVertexLabels_cons_succ v i₀ p e d i j.castSucc).symm
  | _, cons q g, d, j => by
    obtain ⟨d, i⟩ := d
    simp only [comp_cons, degreesErase_cons]
    rcases Fin.eq_zero_or_eq_succ (n := (p.comp q).length) j with rfl | ⟨k, rfl⟩
    · simp [loopErasureArrow_cons_zero]
    · simp [loopErasureArrow_cons_succ, reverseVertexLabels_loopErasure_castSucc q d k]

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
    simp only [comp_nil, degreesErase_nil]
    rcases Fin.eq_zero_or_eq_succ (n := (p.comp nil).length) j with rfl | ⟨k, rfl⟩
    · rw [loopErasureParameter_zero p e nil]
      exact (Degrees.reverseVertexLabels_zero v i₀ p d).trans (congrArg (v b) hd.symm)
    · rw [loopErasureParameter_succ p e nil k, loopErasureArrow_nil p e k]
      simp
  | _, cons q g, d, hd, j => by
    obtain ⟨d, i⟩ := d
    rw [degreesComp_cons (ι := ι)] at hd
    simp only [comp_cons, degreesErase_cons]
    rcases Fin.eq_zero_or_eq_succ (n := (p.comp q).length + 1) j with rfl | ⟨k, rfl⟩
    · exact (Degrees.reverseVertexLabels_cons_zero ..).trans
        ((Degrees.reverseVertexLabels_cons_zero ..).symm.trans
          (congrArg _ (loopErasureParameter_zero p e (q.cons g)).symm))
    · simp only [loopErasureParameter_cons_succ, Degrees.reverseVertexLabels_cons_succ]
      exact reverseVertexLabels_loopErasureParameter q d hd k

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
    simp [hd.symm]
  | _, cons q g, d, hd => by
    obtain ⟨d, i⟩ := d
    rw [degreesComp_cons (ι := ι)] at hd
    rw [loopIndex_cons]
    calc _ = Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d (loopIndex p e q).succ :=
          Degrees.reverseVertexLabels_cons_succ v i₀ _ g _ i (loopIndex p e q).succ
      _ = Degrees.reverseVertexLabels v i₀ ((p.cons e).comp q) d (loopIndex p e q).castSucc :=
          reverseVertexLabels_loopIndex_eq q d hd
      _ = _ := (Degrees.reverseVertexLabels_cons_succ v i₀ _ g _ i
          (loopIndex p e q).castSucc).symm
end Erasure

section Homogeneous

variable {Q R M ι : Type*} [Quiver Q] [Semiring R]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (T : ∀ {b c : Q}, (b ⟶ c) → Module.End R M)
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] {a : Q}

/-- A path history agrees with the finite sequence history of its reversed labels. -/
theorem homogeneousHistory_eq_reverseLabels (i₀ : ι) {b : Q} (p : Path a b)
    (d : p.Degrees (fun _ => ι)) (x : M) :
    p.homogeneousHistory T (fun _ => ℳ) d x =
      Mei.homogeneousHistory ℳ (p.reverseArrowLabels T)
        (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)) x := by
  induction p with
  | nil =>
    simp only [homogeneousHistory_nil, reverseArrowLabels_nil,
      Degrees.reverseVertexLabels_nil, LinearMap.id_apply]
    have hzero :
        Mei.homogeneousHistory ℳ (Fin.elim0 : Fin 0 → Module.End R M)
          (Fin.init (α := fun _ : Fin 1 => ι) (fun _ : Fin 1 => i₀)) = LinearMap.id :=
      Mei.homogeneousHistory_zero ℳ _ _
    have heq : (nil : Path a a).length = 0 := length_nil
    cases heq
    exact Eq.symm (congrFun (congrArg DFunLike.coe hzero) x)
  | cons p e ih =>
    have hi :
        Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ (p.cons e) d) =
          Fin.cons d.2 (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d.1)) := by
      obtain ⟨d, i⟩ := d
      rw [Degrees.reverseVertexLabels_cons]
      funext j
      exact Fin.cases rfl (fun j => rfl) j
    rw [reverseArrowLabels_cons, hi]
    simp only [length_cons]
    rw [Mei.homogeneousHistory_succ_apply, homogeneousHistory_cons_apply, ih d.1]
    rfl

end Homogeneous

end Quiver.Path
