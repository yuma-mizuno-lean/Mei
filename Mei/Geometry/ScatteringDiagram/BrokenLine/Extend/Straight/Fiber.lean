/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Straight

/-!
# Weighted fibers of unchanged terminal encounter blocks

Reattach a prescribed straight block of encounters to all incoming decorated rays
of a fixed final degree. If each added crossing fixes that degree's diagonal
component, attachment embeds the incoming fiber and preserves its whole weights.
Its image consists exactly of the outgoing rays with that unchanged terminal
degree whose earlier history admits the chosen incoming endpoint. Consequently
the sum over this image equals the entire incoming fiber sum of that degree.

The endpoint test retains wall and singular avoidance and the original incoming
source. It is essential: an arbitrary outgoing history need not admit a fixed
earlier endpoint. Empty blocks, infinite gradings, equal spatial velocities and
cancellation of weights are allowed.

We use `DecoratedAdmissibleRay.extendStraight`,
`mem_decoratedHistorySupport_append`, uniqueness of fixed-history realizations
and Mathlib's `Fintype.sum_of_injective`. The image argument extends
`DecoratedAdmissibleRay.mem_range_finalEncounterEmbedding` to a complete unchanged
terminal block. This is the weight-preserving terminal part of the last-change
recursion in Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
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
  {W : J → Set V} {S : K → Set V} {C : Set V}
  (U : Fin m → Module.End R M) (q : Γ) (Y : V)
  (hU : ∀ j x, x ∈ ℳ q → (DirectSum.decompose ℳ (U j x) q : M) = x)
  (L : ℝ) (hL : 0 ≤ L) (τ : Fin m → ℝ)
  (hτ : StrictAnti τ) (hpos : ∀ j, 0 < τ j) (hlt : ∀ j, τ j < L)
  (g : Fin m → V →L[ℝ] ℝ) (b : Fin m → ℝ) (H : Fin m → Set V)
  (htrans : ∀ j, g j (v q) ≠ 0)
  (hheight : ∀ j, g j (Y - τ j • v q) = b j)
  (hinc : ∀ j, Y - τ j • v q ∈ H j)
  (hW : ∀ j u, 0 < u → u ≤ L → (∀ i, u ≠ τ i) → Y - u • v q ∉ W j)
  (hS : ∀ j u, 0 < u → u ≤ L → Y - u • v q ∉ S j)

local notation "D" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Y
local notation "A" => {r : D //
  Fin.snoc (α := fun _ => Γ) (Subtype.val (Sigma.fst r)) p₀ 0 = q}
local notation "E" => DecoratedAdmissibleRay ℳ (Fin.append U T) p₀ a v
  (Fin.append g f) (Fin.append b c)
  (Fin.append (fun j => SignType.sign (g j (v q))) ε)
  (Fin.append H P) W S C (Y - L • v q)

private def attachStraight (r : A) : E := by
  let z := r.val.extendStraight U
    (by rw [r.property]; exact hU) L hL τ hτ hpos hlt g b H
    (by simpa only [← r.property] using htrans)
    (by simpa only [← r.property] using hheight)
    (by simpa only [← r.property] using hinc)
    (by simpa only [← r.property] using hW)
    (by simpa only [← r.property] using hS)
  exact ⟨⟨z.1.val, by simpa only [r.property] using z.1.property⟩,
    { z.2 with
      endpoint_eq := by simpa only [r.property] using z.2.endpoint_eq
      off_walls := by simpa only [r.property] using z.2.off_walls }⟩

private theorem history_attachStraight (r : A) :
    (attachStraight U q Y hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS r).1.val =
      Fin.append (fun _ : Fin m => q) r.val.1.val := by
  simp only [attachStraight, history_extendStraight, r.property]

/-- Reattaching a fixed unchanged-degree terminal block embeds the entire
incoming ray fiber of degree `q`, without identifying equal weights. -/
def straightTerminalEmbedding : A ↪ E where
  toFun := attachStraight U q Y hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS
  inj' := by
    intro r s he
    apply Subtype.ext
    apply Sigma.fst_injective
    apply Subtype.ext
    have hh := congrArg (fun z : E => z.1.val) he
    rw [history_attachStraight, history_attachStraight] at hh
    exact funext fun j => by simpa only [Fin.append_right] using congrFun hh (Fin.natAdd m j)

/-- The attached history repeats `q` on the new block and retains every older
degree. This also recovers the incoming history on the embedding's image. -/
@[simp]
theorem history_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding U q Y hU L hL τ hτ hpos hlt g b H
      htrans hheight hinc hW hS r).1.val =
        Fin.append (fun _ : Fin m => q) r.val.1.val := by
  exact history_attachStraight U q Y hU L hL τ hτ hpos hlt g b H htrans hheight hinc hW hS r

/-- An unchanged terminal block preserves the whole final decoration. -/
@[simp↓]
theorem decoration_straightTerminalEmbedding (r : A) :
    (straightTerminalEmbedding U q Y hU L hL τ hτ hpos hlt g b H
      htrans hheight hinc hW hS r).decoration 0 = r.val.decoration 0 := by
  simp only [decoration_zero, history_straightTerminalEmbedding, homogeneousHistory_append,
    LinearMap.comp_apply]
  apply homogeneousHistory_const_of_decompose_self hU
  simpa only [coe_homogeneousHistoryResult, r.property] using
    (homogeneousHistoryResult ℳ T r.val.1.val a).property

/-- An outgoing ray is an attachment precisely when all added degrees and
their incoming boundary degree are `q` and its earlier history admits `Y`.
The admission test includes every wall, singular set and the incoming source. -/
@[simp↓]
theorem mem_range_straightTerminalEmbedding (z : E) :
    z ∈ Set.range (straightTerminalEmbedding U q Y hU L hL τ hτ hpos hlt g b H
      htrans hheight hinc hW hS) ↔
      (∀ j : Fin m, z.1.val (Fin.castAdd n j) = q) ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val (Fin.natAdd m j)) p₀ 0 = q ∧
        Y ∈ admissibleBackwardDomain f c
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val (Fin.natAdd m i)) p₀ j)) P W S C := by
  constructor
  · rintro ⟨r, rfl⟩
    simp only [history_straightTerminalEmbedding, Fin.append_left, Fin.append_right]
    exact ⟨fun _ => trivial, r.property, r.val.2.mem_admissibleBackwardDomain⟩
  · rintro ⟨hq, hp, hY⟩
    let pp : Fin n → Γ := fun j => z.1.val (Fin.natAdd m j)
    have hh : z.1.val = Fin.append (fun _ : Fin m => q) pp := by
      rw [← Fin.append_castAdd_natAdd (f := z.1.val)]
      congr 1
      exact funext hq
    have hpp : pp ∈ decoratedHistorySupport ℳ T p₀ a v f ε := by
      have hz := z.1.property
      rw [hh] at hz
      exact ((mem_decoratedHistorySupport_append ..).mp hz).1
    let r : D := ⟨⟨pp, hpp⟩, admissibleRayRealization _ _ _ _ _ _ _ _ hY⟩
    refine ⟨⟨r, hp⟩, ?_⟩
    apply Sigma.fst_injective
    apply Subtype.ext
    rw [history_straightTerminalEmbedding]
    exact hh.symm

include hU hL hτ hpos hlt htrans hheight hinc hW hS

open Classical in
/-- Sum the exact outgoing attachment image across a complete unchanged
terminal block. It equals the incoming degree-`q` fiber sum. All older histories
and their multiplicities survive, even when weights cancel. The selection on
the earlier history can, for example, fix the last degree-changing encounter. -/
theorem sum_ite_decoration_straightTerminal_eq_sum (B : (Fin n → Γ) → Prop) :
    (let := Fintype.ofFinite E
     ∑ z : E,
      if (∀ j : Fin m, z.1.val (Fin.castAdd n j) = q) ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val (Fin.natAdd m j)) p₀ 0 = q ∧
        Y ∈ admissibleBackwardDomain f c
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val (Fin.natAdd m i)) p₀ j)) P W S C ∧
        B (fun j => z.1.val (Fin.natAdd m j))
      then z.decoration 0 else 0) =
    (let := Fintype.ofFinite D
     ∑ r : D, if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = q ∧ B r.1.val
       then r.decoration 0 else 0) := by
  classical
  let := Fintype.ofFinite D
  let := Fintype.ofFinite E
  let := Fintype.ofFinite A
  trans ∑ r : A, if B r.val.1.val then r.val.decoration 0 else 0
  · symm
    let e : A ↪ E := straightTerminalEmbedding U q Y hU L hL τ hτ hpos hlt g b H
      htrans hheight hinc hW hS
    apply Fintype.sum_of_injective e e.injective
    · intro z hz
      rw [ite_eq_right]
      exact fun h => hz ((mem_range_straightTerminalEmbedding ..).mpr ⟨h.1, h.2.1, h.2.2.1⟩)
    · intro r
      have hr := (mem_range_straightTerminalEmbedding U q Y hU L hL τ hτ hpos hlt g b H
        htrans hheight hinc hW hS (e r)).mp ⟨r, rfl⟩
      simp only [e, history_straightTerminalEmbedding, Fin.append_left, Fin.append_right] at hr ⊢
      by_cases hB : B r.val.1.val
      · rw [ite_eq_left hB, ite_eq_left ⟨hr.1, hr.2.1, hr.2.2, hB⟩]
        exact (decoration_straightTerminalEmbedding ..).symm
      · rw [ite_eq_right hB, ite_eq_right (fun h => hB h.2.2.2)]
  · apply Fintype.sum_of_injective (Subtype.val : A → D) Subtype.val_injective
    · intro r hr
      rw [ite_eq_right (fun hp => hr ⟨⟨r, hp.1⟩, rfl⟩)]
    · intro r
      by_cases hB : B r.val.1.val
      · rw [ite_eq_left hB, ite_eq_left ⟨r.property, hB⟩]
      · rw [ite_eq_right hB, ite_eq_right (fun h => hB h.2)]

end Mei.DecoratedAdmissibleRay
