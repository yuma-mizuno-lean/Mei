/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mei.LinearAlgebra.GradedModule.History.Path

/-!
# Component expansions of zero-extended transfers

The *total transfer* of a graded correspondence is its total left lift followed by
the right leg. On an admissible homogeneous piece it is the lift across the span,
whose homogeneous components are the transfers; it vanishes on inadmissible pieces.
It is linear on mixed inputs, so graded correspondences on the arrows of a quiver,
between the decomposed modules at their endpoints, give linear arrow maps between
differently graded chamber modules.

The path histories of total transfers are the finite component expansion of
transfer compositions. Each step selects one transfer component of the whole previous
decoration, and the step is zero when that decoration has inadmissible degree. For a fixed
input the nonzero histories are finite and sum to the composite of total transfers, by
`Quiver.Path.sum_homogeneousHistory`.

Correspondence morphisms with common chamber maps at incident arrows intertwine total
transfers provided target total transfers kill the images of inadmissible source pieces
(`Hom.right_comp_totalTransfer`); reflecting admissible degrees suffices. The regrading
theorems `Quiver.Path.homogeneousHistory_map_eq_sum` and
`Quiver.Path.map_homogeneousHistory_of_injective` then apply to transfer histories: a
target history is the grouped sum of its source refinements, and injective degree maps
give componentwise naturality, for example under coefficient truncation.

The single-step formula is `decompose_right_liftLeftTotal_of_mem`.
-/

public noncomputable section

namespace Mei.GradedCorrespondence

variable {R : Type*} [Semiring R] {Q : Type*} [Quiver Q]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]
  {B : ∀ {b c : Q}, (b ⟶ c) → Type*} [∀ (b c : Q) (e : b ⟶ c), AddCommMonoid (B e)]
  [∀ (b c : Q) (e : b ⟶ c), Module R (B e)]
  {I : ∀ {b c : Q}, (b ⟶ c) → Set (ι b)} {J : ∀ {b c : Q}, (b ⟶ c) → Set (ι c)}
  (C : ∀ {b c : Q} (e : b ⟶ c), GradedCorrespondence (B := B e) (ℳ b) (ℳ c) (I e) (J e))

/-- Each step of a transfer history selects one transfer component of the whole
previous decoration. A decoration of inadmissible degree contributes zero. -/
theorem homogeneousHistory_totalTransfer_cons_apply {a b c : Q} (p : Quiver.Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (j : ι c) (x : M a) {i : ι b} [Decidable (i ∈ I e)]
    (hx : p.homogeneousHistory (fun e => (C e).totalTransfer) ℳ d x ∈ ℳ b i) :
    (p.cons e).homogeneousHistory (fun e => (C e).totalTransfer) ℳ
        ((d, j) : (p.cons e).Degrees ι) x =
      if hi : i ∈ I e then ((C e).transfer ⟨i, hi⟩ j ⟨_, hx⟩ : M c) else 0 := by
  rw [Quiver.Path.homogeneousHistory_cons_apply, totalTransfer_apply,
    (C e).decompose_right_liftLeftTotal_of_mem hx]
  split_ifs <;> rfl

/-- A transfer history whose decoration before the final crossing has inadmissible
degree vanishes. -/
theorem homogeneousHistory_totalTransfer_cons_eq_zero_of_notMem {a b c : Q}
    (p : Quiver.Path a b) (e : b ⟶ c) (d : p.Degrees ι) (j : ι c) (x : M a) {i : ι b}
    (hi : i ∉ I e)
    (hx : p.homogeneousHistory (fun e => (C e).totalTransfer) ℳ d x ∈ ℳ b i) :
    (p.cons e).homogeneousHistory (fun e => (C e).totalTransfer) ℳ
        ((d, j) : (p.cons e).Degrees ι) x = 0 := by
  classical
  rw [homogeneousHistory_totalTransfer_cons_apply ℳ C p e d j x hx, dite_eq_right hi]

end Mei.GradedCorrespondence
