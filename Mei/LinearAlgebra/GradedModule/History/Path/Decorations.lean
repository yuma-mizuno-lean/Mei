/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Combinatorics.Quiver.Path.Labels
public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.LinearAlgebra.GradedModule.History.Path.Labels
/-!
# The decorations of a complete component history

For arrow maps between copies of one graded semimodule, extract all intermediate
whole decorations in backward order. The tuple includes the original input and
the final component. A surviving final component forces every entry to be
nonzero. The component propagation equations connect algebraic path histories
to geometric encounter bounds that inspect each decoration separately.
The entries are `Mei.homogeneousHistoryStage` applied to the backward arrow maps
and outgoing vertex labels. The incoming label is restored by
`Fin.snoc_init_self` in the membership statement.
-/

public section

namespace Quiver.Path

variable {Q R M ι : Type*} [Quiver Q] [Semiring R]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (T : ∀ {b c : Q}, (b ⟶ c) → Module.End R M)
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] {a : Q}

/-- All whole component decorations, from the terminal value back to the input.
Equal adjacent values still occupy separate entries. -/
def reverseHomogeneousDecorations (i₀ : ι) (x : M) {b : Q} (p : Path a b)
    (d : p.Degrees (fun _ => ι)) : Fin (p.length + 1) → M :=
  fun j => Mei.homogeneousHistoryStage ℳ (p.reverseArrowLabels T)
    (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)) j x

private theorem homogeneousHistory_eq_reverseLabels (i₀ : ι) {b : Q} (p : Path a b)
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

/-- Every decoration lies in the degree recorded on its segment. -/
theorem reverseHomogeneousDecorations_mem (i₀ : ι) {x : M} (hx : x ∈ ℳ i₀)
    {b : Q} (p : Path a b) (d : p.Degrees (fun _ => ι)) (j : Fin (p.length + 1)) :
    p.reverseHomogeneousDecorations T ℳ i₀ x d j ∈
      ℳ (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d j) := by
  have h := Mei.homogeneousHistoryStage_mem_snoc ℳ (p.reverseArrowLabels T)
    (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)) i₀ ⟨x, hx⟩ j
  have hs := Fin.snoc_init_self
    (q := Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)
  rw [Degrees.reverseVertexLabels_last] at hs
  simp only [reverseHomogeneousDecorations]
  rw [← hs]
  simpa only [Fin.init_snoc] using h

/-- A surviving history has no zero intermediate decoration. -/
theorem reverseHomogeneousDecorations_ne_zero (i₀ : ι) {x : M} {b : Q} (p : Path a b)
    (d : p.Degrees (fun _ => ι)) (hx : p.homogeneousHistory T (fun _ => ℳ) d x ≠ 0) :
    ∀ j, p.reverseHomogeneousDecorations T ℳ i₀ x d j ≠ 0 := by
  rw [homogeneousHistory_eq_reverseLabels T ℳ i₀ p d x] at hx
  simp only [reverseHomogeneousDecorations]
  exact Mei.homogeneousHistoryStage_ne_zero ℳ (p.reverseArrowLabels T)
    (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)) hx

/-- Every encounter applies its arrow map and selects the entire component of
the recorded outgoing degree. -/
theorem reverseHomogeneousDecorations_propagation (i₀ : ι) (x : M) {b : Q} (p : Path a b)
    (d : p.Degrees (fun _ => ι)) (j : Fin p.length) :
    p.reverseHomogeneousDecorations T ℳ i₀ x d j.castSucc =
      Mei.homogeneousComponent ℳ (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d j.castSucc)
        (p.reverseArrowLabels T j (p.reverseHomogeneousDecorations T ℳ i₀ x d j.succ)) := by
  simp only [reverseHomogeneousDecorations, Mei.homogeneousComponent_apply]
  exact Mei.homogeneousHistoryStage_castSucc_apply ℳ (p.reverseArrowLabels T)
    (Fin.init (Degrees.reverseVertexLabels (fun _ i => i) i₀ p d)) j x

end Quiver.Path
