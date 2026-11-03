/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mei.LinearAlgebra.GradedModule.History.Chain

/-!
# Component expansions of zero-extended transfers

The *total transfer* of a graded correspondence is its total left lift followed by
the right leg. On an admissible homogeneous piece it is the lift across the span,
whose homogeneous components are the transfers; it vanishes on inadmissible pieces.
It is linear on mixed inputs, so a sequence of correspondences `C k` from `M (k + 1)`
to `M k` forms a chain of linear maps between differently graded chamber modules.

The chain histories of total transfers are the finite component expansion of
transfer compositions. Each step selects one transfer component of the whole previous
decoration, and the step is zero when that decoration has inadmissible degree. For a fixed
input the nonzero histories are finite and sum to the composite of total transfers, by
`sum_chainHistory`.

Correspondence morphisms with common chamber maps at incident steps intertwine total
transfers provided target total lifts kill the images of inadmissible source pieces.
Reflecting admissible degrees suffices. With `comp_totalTransfer_of_hom`, the regrading
theorems `chainHistory_map_eq_sum` and `map_chainHistory_of_injective` apply to transfer
histories: a target history is the grouped sum of its source refinements, and injective
degree maps give componentwise naturality, for example under coefficient truncation.

The single-step API, `totalTransfer` and its naturality `Hom.right_comp_totalTransfer` and
`comp_totalTransfer_of_hom`, lives in `GradedCorrespondence/Basic.lean` and
`GradedCorrespondence/Hom.lean`; the single-step formula is
`decompose_right_liftLeftTotal_of_mem`.
-/

public noncomputable section

namespace Mei.GradedCorrespondence

section Chain

variable {R : Type*} [Semiring R]
  {M : ℕ → Type*} [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]
  {ι : ℕ → Type*} [∀ k, DecidableEq (ι k)] (ℳ : ∀ k, ι k → Submodule R (M k))
  [∀ k, DirectSum.Decomposition (ℳ k)]
  {B : ℕ → Type*} [∀ k, AddCommMonoid (B k)] [∀ k, Module R (B k)]
  {I : ∀ k, Set (ι (k + 1))} {J : ∀ k, Set (ι k)}
  (C : ∀ k, GradedCorrespondence (B := B k) (ℳ (k + 1)) (ℳ k) (I k) (J k))

/-- Each step of a transfer history selects one transfer component of the whole
previous decoration. A decoration of inadmissible degree contributes zero. -/
theorem chainHistory_totalTransfer_succ_apply {n : ℕ} (p : (j : Fin (n + 1)) → ι j)
    (a : M (n + 1)) {i : ι 1} [Decidable (i ∈ I 0)]
    (hx : chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => (C (j + 1)).totalTransfer) (fun j => p (j.chainSucc)) a ∈
        ℳ 1 i) :
    chainHistory ℳ (fun j => (C j).totalTransfer) p a =
      if hi : i ∈ I 0 then ((C 0).transfer ⟨i, hi⟩ (p (n.chainHead)) ⟨_, hx⟩ : M 0) else 0 := by
  rw [chainHistory_succ_apply, totalTransfer_apply,
    (C 0).decompose_right_liftLeftTotal_of_mem hx]
  split_ifs <;> rfl

/-- A transfer history whose decoration before the final crossing has inadmissible
degree vanishes. -/
theorem chainHistory_totalTransfer_eq_zero_of_not_mem {n : ℕ} (p : (j : Fin (n + 1)) → ι j)
    (a : M (n + 1)) {i : ι 1} (hi : i ∉ I 0)
    (hx : chainHistory (M := fun k => M (k + 1)) (ι := fun k => ι (k + 1))
      (fun k => ℳ (k + 1)) (fun j => (C (j + 1)).totalTransfer) (fun j => p (j.chainSucc)) a ∈
        ℳ 1 i) :
    chainHistory ℳ (fun j => (C j).totalTransfer) p a = 0 := by
  classical
  rw [chainHistory_totalTransfer_succ_apply ℳ C p a hx, dite_eq_right hi]

end Chain

end Mei.GradedCorrespondence
