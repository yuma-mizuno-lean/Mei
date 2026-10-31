/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Subtype

/-!
# Concatenation of homogeneous propagation histories

A history along two consecutive sequences is the composite of its two
histories. Since indices run backwards, the right block acts first. Surviving
histories of the concatenation correspond exactly to a surviving right history
followed by a surviving left history on its whole output decoration. In
particular, intermediate decorations that vanish contribute no histories.

`homogeneousHistorySupportAppendEquiv` gives this correspondence without a
finite grading or finite-dimensional coefficient modules. It retains the degree
history of each block and the whole final decoration. The resulting finite-sum
formula allows local propagation histories to be attached to exterior histories
without changing their weights or identifying distinct intermediate degrees.

The construction uses `homogeneousHistory`, `homogeneousHistorySupport` and
their finite-support expansion from `Mei.LinearAlgebra.GradedModule.History.Finite`,
together with Mathlib's `Fin.appendEquiv`.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

variable {n m : ℕ} (T : Fin n → Module.End R M) (U : Fin m → Module.End R M) (a : M)

/-- Surviving histories of two consecutive blocks are exactly pairs of
surviving histories, with the second history starting at the first one's whole
decoration. The first sigma coordinate is the right block, which acts first. -/
def homogeneousHistorySupportAppendEquiv :
    (homogeneousHistorySupport ℳ (Fin.append T U) a : Type _) ≃
      Σ q : (homogeneousHistorySupport ℳ U a : Type _),
        (homogeneousHistorySupport ℳ T (homogeneousHistory ℳ U q.val a) : Type _) where
  toFun r := by
    let p := fun j => r.val (Fin.castAdd m j)
    let q := fun j => r.val (Fin.natAdd n j)
    have he : Fin.append p q = r.val := (Fin.appendEquiv n m).apply_symm_apply r.val
    have hr : homogeneousHistory ℳ (Fin.append T U) (Fin.append p q) a ≠ 0 := by
      rw [he]
      exact (mem_homogeneousHistorySupport ..).mp r.property
    exact ⟨⟨q, (mem_homogeneousHistorySupport ..).mpr
      (homogeneousHistory_right_ne_zero ℳ T U p q hr)⟩,
      ⟨p, (mem_homogeneousHistorySupport ..).mpr (by
        simpa only [homogeneousHistory_append, LinearMap.comp_apply] using hr)⟩⟩
  invFun r := ⟨Fin.append r.2.val r.1.val,
    by simpa only [mem_homogeneousHistorySupport, homogeneousHistory_append,
      LinearMap.comp_apply] using (mem_homogeneousHistorySupport ..).mp r.2.property⟩
  left_inv r := Subtype.ext Fin.append_castAdd_natAdd
  right_inv r := by
    rcases r with ⟨⟨q, hq⟩, ⟨p, hp⟩⟩
    apply Sigma.ext (Subtype.ext (funext fun j => Fin.append_right p q j))
    apply (Subtype.heq_iff_coe_eq (fun x => by simp)).mpr
    exact funext fun j => Fin.append_left p q j

/-- Splitting a history records exactly its degrees in the right block. -/
@[simp]
theorem homogeneousHistorySupportAppendEquiv_fst
    (r : (homogeneousHistorySupport ℳ (Fin.append T U) a : Type _)) :
    (homogeneousHistorySupportAppendEquiv ℳ T U a r).1.val =
      fun j => r.val (Fin.natAdd n j) := (rfl)

/-- Splitting a history records exactly its degrees in the left block. -/
@[simp]
theorem homogeneousHistorySupportAppendEquiv_snd
    (r : (homogeneousHistorySupport ℳ (Fin.append T U) a : Type _)) :
    (homogeneousHistorySupportAppendEquiv ℳ T U a r).2.val =
      fun j => r.val (Fin.castAdd m j) := (rfl)

/-- Joining histories appends their degree lists in backward order. -/
@[simp]
theorem homogeneousHistorySupportAppendEquiv_symm_val
    (r : Σ q : (homogeneousHistorySupport ℳ U a : Type _),
      (homogeneousHistorySupport ℳ T (homogeneousHistory ℳ U q.val a) : Type _)) :
    ((homogeneousHistorySupportAppendEquiv ℳ T U a).symm r).val =
      Fin.append r.2.val r.1.val := (rfl)

/-- The splitting correspondence preserves whole final decorations. -/
theorem homogeneousHistorySupportAppendEquiv_decoration
    (r : (homogeneousHistorySupport ℳ (Fin.append T U) a : Type _)) :
    homogeneousHistory ℳ T (homogeneousHistorySupportAppendEquiv ℳ T U a r).2.val
        (homogeneousHistory ℳ U (homogeneousHistorySupportAppendEquiv ℳ T U a r).1.val a) =
      homogeneousHistory ℳ (Fin.append T U) r.val a := by
  simp only [homogeneousHistorySupportAppendEquiv_fst, homogeneousHistorySupportAppendEquiv_snd]
  rw [← LinearMap.comp_apply, ← homogeneousHistory_append, Fin.append_castAdd_natAdd]

open Classical in
/-- Selecting concatenated histories by any condition on their two blocks
commutes with the iterated finite sum. Conditions may depend on both degree
histories; no finiteness of the grading is required. -/
theorem sum_ite_homogeneousHistory_append (E : (Fin n → ι) → (Fin m → ι) → Prop) :
    (∑ r : (homogeneousHistorySupport ℳ (Fin.append T U) a : Type _),
        if E (fun j => r.val (Fin.castAdd m j)) (fun j => r.val (Fin.natAdd n j))
        then homogeneousHistory ℳ (Fin.append T U) r.val a else 0) =
      ∑ q : (homogeneousHistorySupport ℳ U a : Type _),
        ∑ p : (homogeneousHistorySupport ℳ T (homogeneousHistory ℳ U q.val a) : Type _),
          if E p.val q.val then homogeneousHistory ℳ T p.val
            (homogeneousHistory ℳ U q.val a) else 0 := by
  classical
  let F (r : Σ q : (homogeneousHistorySupport ℳ U a : Type _),
      (homogeneousHistorySupport ℳ T (homogeneousHistory ℳ U q.val a) : Type _)) : M :=
    if E r.2.val r.1.val then homogeneousHistory ℳ T r.2.val
      (homogeneousHistory ℳ U r.1.val a) else 0
  calc
    _ = ∑ r, F r := by
      apply Fintype.sum_equiv (homogeneousHistorySupportAppendEquiv ℳ T U a)
      intro r
      simp only [F, homogeneousHistorySupportAppendEquiv_fst,
        homogeneousHistorySupportAppendEquiv_snd]
      split_ifs
      · exact (homogeneousHistorySupportAppendEquiv_decoration ℳ T U a r).symm
      · rfl
    _ = _ := Fintype.sum_sigma F

end Mei
