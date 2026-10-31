/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.FunctionWall.Basic
public import Mei.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.RingTheory.Ideal.Quotient
public import Mei.Algebra.Group.Units.Hom

/-!
# Coefficient order of function-wall histories

A wall function congruent to one modulo an ideal acts as the identity modulo
the next ideal power on a homogeneous input. This holds for negative normal
weights too, so it applies to either crossing orientation.

For a finer exponent grading and a homogeneous coefficient ideal, selecting a
different exponent therefore raises coefficient order. Along an actual sequence
of function-wall component maps the increases accumulate: a nonzero history has
fewer degree changes than the nilpotency index of the coefficient ideal. Encounters
preserving degree are retained and cost no increase. This is the ordinary-wall
coefficient-order argument in Gross–Hacking–Siebert, *Theta functions on varieties
with effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4).

We use `functionWallAction_apply_of_mem`, Mathlib's homogeneous ideals and ideal
quotients, and the existing whole-component maps `Mei.homogeneousHistory`.
-/

public noncomputable section

namespace Mei.GradedAlgebra

variable {R A : Type*} [CommSemiring R]

section Semiring

variable [CommSemiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- Function walls preserve the ideal order of a weight-homogeneous input. -/
theorem functionWallAction_mem_pow (f : (𝒜 0)ˣ) {w : ℤ} {a : A}
    (ha : a ∈ 𝒜 w) {b : ℕ} (hb : a ∈ I ^ b) :
    functionWallAction 𝒜 f a ∈ I ^ b := by
  rw [functionWallAction_apply_of_mem 𝒜 f ha]
  exact Ideal.mul_mem_right _ _ hb

end Semiring

variable [CommRing A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- On a weight-homogeneous input of ideal order `b`, a function wall congruent
to one changes the input only in order `b + 1`, for every integer weight. -/
theorem functionWallAction_sub_mem_pow (f : (𝒜 0)ˣ)
    (hf : algebraMap (𝒜 0) A f - 1 ∈ I) {w : ℤ} {a : A}
    (ha : a ∈ 𝒜 w) {b : ℕ} (hb : a ∈ I ^ b) :
    functionWallAction 𝒜 f a - a ∈ I ^ (b + 1) := by
  have hp : algebraMap (𝒜 0) A (f ^ w : (𝒜 0)ˣ) - 1 ∈ I := by
    rw [map_units_zpow]
    exact I.zpow_sub_one_mem (Units.map (algebraMap (𝒜 0) A).toMonoidHom f) hf w
  rw [functionWallAction_apply_of_mem 𝒜 f ha]
  convert Ideal.mul_mem_mul hb hp using 1 <;> simp [pow_succ, mul_sub]

variable {Γ : Type*} [AddMonoid Γ] [DecidableEq Γ]
  (𝒢 : Γ → Submodule R A) [GradedAlgebra 𝒢]

/-- An entire component in a different exponent has one higher ideal order.
The exponent grading may be strictly finer than the wall's normal-weight grading. -/
theorem decompose_functionWallAction_mem_pow_succ
    (hI : I.IsHomogeneous 𝒢) (f : (𝒜 0)ˣ)
    (hf : algebraMap (𝒜 0) A f - 1 ∈ I) {w : ℤ} {a : A}
    (ha : a ∈ 𝒜 w) {b : ℕ} (hb : a ∈ I ^ b)
    {p q : Γ} (hp : a ∈ 𝒢 p) (hpq : p ≠ q) :
    (DirectSum.decompose 𝒢 (functionWallAction 𝒜 f a) q : A) ∈ I ^ (b + 1) := by
  have hh := ((hI.pow (b + 1)).mem_iff.mp
    (functionWallAction_sub_mem_pow 𝒜 I f hf ha hb)) q
  have he := congrArg (fun x : A => (DirectSum.decompose 𝒢 x q : A))
    (sub_add_cancel (functionWallAction 𝒜 f a) a)
  simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.decompose_of_mem_ne 𝒢 hp hpq, add_zero] at he
  rwa [he] at hh

section Histories

variable {n : ℕ} (𝒜s : Fin n → ℤ → Submodule R A)
  [∀ j, GradedAlgebra (𝒜s j)] (f : ∀ j, (𝒜s j 0)ˣ)
  (weight : Fin n → Γ → ℤ)

/-- Each actual function-wall history gains at least one ideal order for each
change of exponent. Same-degree encounters remain in the history. -/
theorem homogeneousHistory_functionWallAction_mem_pow
    (hI : I.IsHomogeneous 𝒢)
    (hf : ∀ j, algebraMap (𝒜s j 0) A (f j) - 1 ∈ I)
    (hw : ∀ j q, 𝒢 q ≤ 𝒜s j (weight j q))
    (r : Fin n → Γ) (p : Γ) (a : 𝒢 p) {b : ℕ} (hb : (a : A) ∈ I ^ b) :
    homogeneousHistory 𝒢 (fun j => (functionWallAction (𝒜s j) (f j)).toLinearMap) r a ∈
      I ^ (b + ∑ j : Fin n, if r j = Fin.snoc (α := fun _ => Γ) r p j.succ then 0 else 1) := by
  induction n generalizing b with
  | zero => simpa using hb
  | succ n ih =>
    let T := fun j => (functionWallAction (𝒜s j) (f j)).toLinearMap
    let x := homogeneousHistory 𝒢 (fun j : Fin n => T j.succ) (fun j => r j.succ) a
    let q := Fin.snoc (α := fun _ => Γ) r p (0 : Fin (n + 1)).succ
    have hx : x ∈ 𝒢 q := by
      simpa only [homogeneousHistoryStage_zero, homogeneousHistoryStage_succ] using
        homogeneousHistoryStage_mem_snoc 𝒢 T r p a (0 : Fin (n + 1)).succ
    have hi := ih (fun j => 𝒜s j.succ) (fun j => f j.succ)
      (fun j => weight j.succ) (fun j => hf j.succ) (fun j => hw j.succ)
      (fun j => r j.succ) hb
    have hsnoc (j : Fin (n + 1)) :
        Fin.snoc (α := fun _ => Γ) r p j.succ =
          Fin.snoc (α := fun _ => Γ) (fun k : Fin n => r k.succ) p j := by
      have h := congrFun (Fin.cons_snoc_eq_snoc_cons (r 0) (Fin.tail r) p) j.succ
      rw [Fin.cons_self_tail, Fin.cons_succ] at h
      simpa only [Fin.tail_def] using h.symm
    simp only [← hsnoc] at hi
    rw [homogeneousHistory_succ_apply, Fin.sum_univ_succ]
    by_cases he : r 0 = q
    all_goals dsimp only [q] at he
    · have hy := ((hI.pow _).mem_iff.mp
        (functionWallAction_mem_pow (𝒜s 0) I (f 0) (hw 0 q hx) hi)) (r 0)
      simpa only [ite_eq_left he, zero_add, T, x, AlgEquiv.toLinearMap_apply] using hy
    · have hy := decompose_functionWallAction_mem_pow_succ (𝒜s 0) I 𝒢 hI
        (f 0) (hf 0) (hw 0 q hx) hi hx (Ne.symm he)
      simpa only [ite_eq_right he, Nat.add_left_comm b 1, Nat.add_assoc,
        Nat.add_comm 1, T, x, AlgEquiv.toLinearMap_apply] using hy

/-- Nilpotency bounds the number of exponent changes in a surviving actual
function-wall history, independently of its number of unchanged-degree encounters. -/
theorem degree_changes_lt_of_homogeneousHistory_functionWallAction_ne_zero
    (hI : I.IsHomogeneous 𝒢)
    (hf : ∀ j, algebraMap (𝒜s j 0) A (f j) - 1 ∈ I)
    (hw : ∀ j q, 𝒢 q ≤ 𝒜s j (weight j q))
    (r : Fin n → Γ) (p : Γ) (a : 𝒢 p) {b s : ℕ} (hb : (a : A) ∈ I ^ b)
    (hs : I ^ s = ⊥)
    (hne : homogeneousHistory 𝒢
      (fun j => (functionWallAction (𝒜s j) (f j)).toLinearMap) r a ≠ 0) :
    b + ∑ j : Fin n, (if r j = Fin.snoc (α := fun _ => Γ) r p j.succ then 0 else 1) < s := by
  by_contra! h
  have hm := homogeneousHistory_functionWallAction_mem_pow I 𝒢 𝒜s f weight
    hI hf hw r p a hb
  have hz := Ideal.pow_le_pow_right h hm
  rw [hs, Ideal.mem_bot] at hz
  exact hne hz

end Histories

end Mei.GradedAlgebra
