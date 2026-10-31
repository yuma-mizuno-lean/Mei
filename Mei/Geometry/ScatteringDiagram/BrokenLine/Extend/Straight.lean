/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Concatenation
public import Mei.Geometry.Convex.Sweep.Admissible.Continue
public import Mei.LinearAlgebra.GradedModule.History.Erasure

/-!
# Reattaching unchanged-degree terminal encounters

Continue an actual decorated ray through a whole straight block of encounters
without changing its final degree. If each new crossing fixes that degree's whole
component, every added segment retains the original final decoration. All older
degrees, decorations, encounters and the admitted incoming tail are retained.
This restores the unchanged encounters after the last positive degree change,
including when that change itself has unchanged spatial velocity.

We combine `AdmissibleRayRealization.continueStraight` with
`mem_decoratedHistorySupport_append` and
`homogeneousHistoryStage_const_of_decompose_self`. This is the terminal-block
attachment used in the backward recursion of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Y : V}
  (r : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Y)

local notation "q" => Fin.snoc (α := fun _ => Γ) (Subtype.val (Sigma.fst r)) p₀ 0

variable (U : Fin m → Module.End R M)
  (hU : ∀ j x, x ∈ ℳ (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0) →
    (DirectSum.decompose ℳ (U j x) (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0) : M) = x)
  (L : ℝ) (hL : 0 ≤ L) (τ : Fin m → ℝ)
  (hτ : StrictAnti τ) (hpos : ∀ j, 0 < τ j) (hlt : ∀ j, τ j < L)
  (g : Fin m → V →L[ℝ] ℝ) (b : Fin m → ℝ) (H : Fin m → Set V)
  (htrans : ∀ j, g j (v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0)) ≠ 0)
  (hheight : ∀ j, g j (Y - τ j • v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0)) = b j)
  (hinc : ∀ j, Y - τ j • v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0) ∈ H j)
  (hW : ∀ a u, 0 < u → u ≤ L → (∀ j, u ≠ τ j) →
    Y - u • v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0) ∉ W a)
  (hS : ∀ a u, 0 < u → u ≤ L → Y - u • v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0) ∉ S a)

include hU in
/-- Reattach a complete straight terminal block, selecting the unchanged whole
component at every added encounter. The maps need only fix the diagonal
component at the final degree; they may create arbitrary other components. -/
def extendStraight :
    DecoratedAdmissibleRay ℳ (Fin.append U T) p₀ a v
      (Fin.append g f) (Fin.append b c)
      (Fin.append (fun j => SignType.sign (g j (v q))) ε)
      (Fin.append H P) W S C (Y - L • v q) := by
  let p : Fin (m + n) → Γ := Fin.append (fun _ : Fin m => q) r.1.val
  have hv : (fun j => v (Fin.snoc (α := fun _ => Γ) p p₀ j)) =
      Fin.append (m := m) (n := n + 1) (fun _ : Fin m => v q)
        (fun j => v (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j)) := by
    dsimp only [p]
    rw [← Fin.append_snoc]
    funext j
    refine Fin.addCases (m := m) (n := n + 1) (fun _ => ?_) (fun _ => ?_) j <;> simp
  refine ⟨⟨p, (mem_decoratedHistorySupport_append ..).mpr ⟨r.1.property, ?_⟩⟩,
    (r.2.continueStraight L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).congrVelocity
      hv.symm⟩
  apply (mem_decoratedHistorySupport ..).mpr
  refine ⟨?_, fun j => ?_⟩
  · rw [homogeneousHistory_const_of_decompose_self hU
      (homogeneousHistoryResult ℳ T r.1.val a).property]
    simpa only [coe_homogeneousHistoryResult, ← decoration_zero] using r.decoration_ne_zero 0
  · simp [Fin.snoc]

/-- Attachment repeats the final degree before the entire original history. -/
@[simp]
theorem history_extendStraight :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).1.val =
      Fin.append (fun _ : Fin m => q) r.1.val := (rfl)

/-- The decorated continuation preserves the complete incoming path, using the
geometric endpoint translation with no new bend increments. -/
@[simp]
theorem ray_extendStraight :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).2.ray =
      r.2.ray.truncate L := by
  simp only [extendStraight, AdmissibleRayRealization.ray_congrVelocity,
    AdmissibleRayRealization.ray_continueStraight]

/-- Every earlier encounter retains its time relative to the incoming path;
new and old encounter parameters are translated by the same `L`. -/
@[simp]
theorem parameter_extendStraight :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).2.parameter =
      Fin.cons 0 (Fin.append (fun j => τ j - L) (fun j => r.2.parameter j.succ - L)) := by
  simp only [extendStraight, AdmissibleRayRealization.parameter_congrVelocity,
    AdmissibleRayRealization.parameter_continueStraight]

/-- All original segment decorations survive unchanged, including the decoration
at the start of the attached block. -/
@[simp]
theorem decoration_natAdd_extendStraight (j : Fin (n + 1)) :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).decoration
      (Fin.natAdd m j) = r.decoration j := by
  simp only [decoration_def, history_extendStraight, homogeneousHistoryStage_natAdd,
    Fin.append_right]

/-- Every segment of the added block, including its incoming boundary segment,
carries the original whole final decoration. -/
@[simp]
theorem decoration_castLE_extendStraight (j : Fin (m + 1)) :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).decoration
      (j.castLE (by omega)) = r.decoration 0 := by
  induction j using Fin.reverseInduction with
  | last =>
    have he : (Fin.last m).castLE (by omega) =
        Fin.natAdd m (0 : Fin (n + 1)) := by ext; simp
    rw [he, decoration_natAdd_extendStraight]
  | cast j ih =>
    have hc : j.castSucc.castLE (by omega) =
        (Fin.castAdd n j).castSucc := by ext; simp
    have hs : (Fin.castAdd n j).succ =
        j.succ.castLE (by omega) := by ext; simp
    rw [hc, decoration_castSucc, history_extendStraight, Fin.append_left, hs, ih]
    rw [Fin.append_left]
    apply hU
    simpa only [decoration_def] using homogeneousHistoryStage_mem_snoc ℳ T r.1.val p₀ a 0

/-- Reattaching an unchanged terminal block preserves the whole final weight,
including when the block is empty. -/
@[simp↓]
theorem decoration_zero_extendStraight :
    (r.extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS).decoration 0 =
      r.decoration 0 := by
  simpa only [Fin.castLE_zero] using
    r.decoration_castLE_extendStraight U hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS 0

end Mei.DecoratedAdmissibleRay
