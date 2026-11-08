/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Path.Labels

/-!
# The decorations of a complete component history

For arrow maps between copies of one graded semimodule, extract all intermediate
whole decorations in backward order. The tuple includes the original input and
the final component. A surviving final component forces every entry to be
nonzero. The component propagation equations connect algebraic path histories
to geometric encounter bounds that inspect each decoration separately.
The entries are the prefix values of `Quiver.Path.homogeneousHistory`.
-/

public section

namespace Quiver.Path

variable {Q R M ι : Type*} [Quiver Q] [Semiring R]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (T : ∀ {b c : Q}, (b ⟶ c) → Module.End R M)
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] {a : Q}

/-- All whole component decorations, from the terminal value back to the input.
Equal adjacent values still occupy separate entries. -/
def reverseHomogeneousDecorations (x : M) :
    {b : Q} → (p : Path a b) → p.Degrees (fun _ => ι) → Fin (p.length + 1) → M
  | _, nil, _ => fun _ => x
  | _, cons p e, d => Fin.cons
      ((p.cons e).homogeneousHistory T (fun _ => ℳ) d x)
      (reverseHomogeneousDecorations x p d.1)

/-- The empty history contains just its input. -/
@[simp]
theorem reverseHomogeneousDecorations_nil (x : M)
    (d : (nil : Path a a).Degrees (fun _ => ι)) :
    (nil : Path a a).reverseHomogeneousDecorations T ℳ x d = fun _ => x := (rfl)

/-- Appending an encounter prepends its entire output component. -/
@[simp]
theorem reverseHomogeneousDecorations_cons (x : M) {b c : Q} (p : Path a b)
    (e : b ⟶ c) (d : p.Degrees (fun _ => ι)) (i : ι) :
    (p.cons e).reverseHomogeneousDecorations T ℳ x (d, i) =
      Fin.cons ((p.cons e).homogeneousHistory T (fun _ => ℳ) (d, i) x)
        (p.reverseHomogeneousDecorations T ℳ x d) := (rfl)

/-- The first backward entry is the terminal whole component. -/
@[simp]
theorem reverseHomogeneousDecorations_zero (x : M) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)),
      p.reverseHomogeneousDecorations T ℳ x d 0 =
        p.homogeneousHistory T (fun _ => ℳ) d x
  | _, nil, _ => by simp only [reverseHomogeneousDecorations_nil, homogeneousHistory_nil,
      LinearMap.id_apply]
  | _, cons _ _, _ => Fin.cons_zero ..

/-- The last backward entry retains the original input. -/
@[simp]
theorem reverseHomogeneousDecorations_last (x : M) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)),
      p.reverseHomogeneousDecorations T ℳ x d (Fin.last p.length) = x
  | _, nil, _ => rfl
  | _, cons p _, d => by
    exact (Fin.cons_succ _ _ (Fin.last p.length)).trans
      (reverseHomogeneousDecorations_last x p d.1)

/-- Every decoration lies in the degree recorded on its segment. -/
theorem reverseHomogeneousDecorations_mem (i₀ : ι) {x : M} (hx : x ∈ ℳ i₀) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)) (j : Fin (p.length + 1)),
      p.reverseHomogeneousDecorations T ℳ x d j ∈
        ℳ (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d j)
  | _, nil, _, _ => by simpa only [reverseHomogeneousDecorations_nil,
      Degrees.reverseVertexLabels_nil] using hx
  | _, cons p e, d, j => by
    obtain ⟨d, i⟩ := d
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [reverseHomogeneousDecorations_zero, Degrees.reverseVertexLabels_zero,
        Degrees.terminalDegree_cons] using homogeneousHistory_cons_mem T (fun _ => ℳ)
          p e d i x
    · rw [reverseHomogeneousDecorations_cons, Degrees.reverseVertexLabels_cons]
      exact reverseHomogeneousDecorations_mem i₀ hx p d j

/-- A surviving history has no zero intermediate decoration. -/
theorem reverseHomogeneousDecorations_ne_zero {x : M} :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)),
      p.homogeneousHistory T (fun _ => ℳ) d x ≠ 0 →
        ∀ j, p.reverseHomogeneousDecorations T ℳ x d j ≠ 0
  | _, nil, _, hx, _ => by simpa only [reverseHomogeneousDecorations_nil,
      homogeneousHistory_nil, LinearMap.id_apply] using hx
  | _, cons p e, d, hx, j => by
    obtain ⟨d, i⟩ := d
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [reverseHomogeneousDecorations_zero] using hx
    · rw [reverseHomogeneousDecorations_cons]
      exact reverseHomogeneousDecorations_ne_zero p d
        (homogeneousHistory_ne_zero_of_cons T (fun _ => ℳ) p e d i hx) j

/-- Every encounter applies its arrow map and selects the entire component of
the recorded outgoing degree. -/
theorem reverseHomogeneousDecorations_propagation (i₀ : ι) (x : M) :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)) (j : Fin p.length),
      p.reverseHomogeneousDecorations T ℳ x d j.castSucc =
        Mei.homogeneousComponent ℳ
          (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d j.castSucc)
          (p.reverseArrowLabels T j (p.reverseHomogeneousDecorations T ℳ x d j.succ))
  | _, nil, _, j => j.elim0
  | _, cons p e, d, j => by
    obtain ⟨d, i⟩ := d
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [length_cons, Fin.castSucc_zero, reverseHomogeneousDecorations_cons,
        Degrees.reverseVertexLabels_cons, reverseArrowLabels_cons,
        Fin.cons_zero, Fin.cons_succ, reverseHomogeneousDecorations_zero]
      rw [homogeneousHistory_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    · simpa only [length_cons, Fin.castSucc_succ, reverseHomogeneousDecorations_cons,
        Degrees.reverseVertexLabels_cons, reverseArrowLabels_cons, Fin.cons_succ] using
        reverseHomogeneousDecorations_propagation i₀ x p d j

end Quiver.Path
