/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.Combinatorics.Quiver.Path.Labels

/-!
# Vertex labels of a complete degree history

Assign values to the chamber degrees visited by a component history. The tuple
starts at the final component and ends at the prescribed incoming degree.
In particular, spatial directions can be extracted without identifying the
different chambers' degree types or coefficient modules. For a uniformly graded
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

end Quiver.Path
