/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Algebra.Lie.Filtered.Correction
public import Mei.LinearAlgebra.ModuleFiltration.Raising

/-!
# Truncated BCH actions are the identity plus a raising part

A filtration-raising Lie action induces the identity on the associated graded. Hence the
finite BCH action of any label is the identity plus an endomorphism that raises the
filtration by one. By `Mei.LinearAlgebra.ModuleFiltration.Raising` that raising part is
nilpotent at finite order and the inverse of the action is its finite geometric series.

This identifies the backward-ray operator of the recursions of `Mei.ModuleProbe` at the
coefficient level: the correction terms of
`shiftedQuotientComponent_truncatedBCHAction_eq_add_sum` are the raising part, and the
recursion terminates after `k + 1` steps at order `k`. The corresponding uniqueness and
expansion statements are `truncatedBCHAction_eq_of_eq_add` and
`truncatedBCHAction_symm_apply_eq_sum`.
-/

public noncomputable section

namespace Mei.ModuleFiltration

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ F]

/-- The correction of a truncated BCH action on a class of order `b` lands in order
`b + 1`: after passing to the order-`b` quotient the action fixes the class. -/
theorem truncatedBCHAction_raisingPart_mem {k : ℕ} (g : d.truncatedGroup ℒ k)
    {b : ℕ} {x : F.quotient k} (hx : x ∈ F.quotientImage k b) :
    F.raisingPart (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k)) x ∈
      F.quotientImage k (b + 1) := by
  obtain ⟨m, hm, rfl⟩ := F.mem_quotientImage.mp hx
  by_cases hbk : b ≤ k
  · have hfix : F.transition hbk
        ((F.truncatedBCHAction d ℒ k g) ((F.submodule (k + 1)).mkQ m)) =
        F.transition hbk ((F.submodule (k + 1)).mkQ m) := by
      rw [F.transition_truncatedBCHAction d ℒ hbk g, Submodule.mkQ_apply,
        F.transition_mk hbk m]
      exact F.truncatedBCHAction_mk_eq_self_of_mem d ℒ b _ hm
    have hker : F.raisingPart (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))
        ((F.submodule (k + 1)).mkQ m) ∈ LinearMap.ker (F.transition hbk) := by
      rw [LinearMap.mem_ker, raisingPart_apply, LinearEquiv.coe_coe, map_sub]
      exact sub_eq_zero.mpr hfix
    rwa [F.ker_transition hbk] at hker
  · have hb : k + 1 ≤ b := by omega
    have hzero : (F.submodule (k + 1)).mkQ m = (0 : F.quotient k) :=
      (Submodule.Quotient.mk_eq_zero _).mpr (F.antitone hb hm)
    rw [raisingPart_apply, hzero, map_zero, sub_self]
    exact Submodule.zero_mem _

/-- The truncated BCH action of any label is the identity plus a filtration-raising part. -/
theorem truncatedBCHAction_isAdapted (k : ℕ) (g : d.truncatedGroup ℒ k) :
    F.IsAdapted k (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k)) :=
  F.isAdapted_iff.mpr (F.isRaisingEnd_iff.mpr (fun _b _ hx =>
    F.truncatedBCHAction_raisingPart_mem d ℒ g hx))

/-- At order `k + 1` the backward operator of a truncated BCH action is the correction
map: the difference from the identity is computed at one lower order. -/
theorem truncatedBCHAction_raisingPart_eq_correction (k : ℕ) (g : d.truncatedGroup ℒ (k + 1))
    (x : F.quotient (k + 1)) :
    F.raisingPart (F.truncatedBCHAction d ℒ (k + 1) g : Module.End R (F.quotient (k + 1))) x =
      F.truncatedBCHCorrection d ℒ k g (F.transition (Nat.le_succ k) x) := by
  rw [raisingPart_apply, LinearEquiv.coe_coe, F.truncatedBCHAction_eq_add_correction d ℒ k g]
  abel

/-- A word of wall crossings is the identity plus a raising part. -/
theorem isAdapted_truncatedBCHAction_list_prod (k : ℕ) (l : List (d.truncatedGroup ℒ k)) :
    F.IsAdapted k ((l.map fun g =>
      (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))).prod) := by
  induction l with
  | nil => simpa using (IsAdapted.one (F := F) (k := k))
  | cons g gs ih =>
    rw [List.map_cons, List.prod_cons]
    exact IsAdapted.mul (F.truncatedBCHAction_isAdapted d ℒ k g) ih

/-- At order `k` the backward operator of a truncated BCH action is nilpotent with the
`(k + 1)`st power zero. -/
theorem truncatedBCHAction_backwardPart_pow_eq_zero (k : ℕ) (g : d.truncatedGroup ℒ k) :
    (F.backwardPart (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))) ^ (k + 1) = 0 :=
  (F.truncatedBCHAction_isAdapted d ℒ k g).backwardPart_pow_eq_zero

/-- Every solution of the component recursion of a truncated BCH action is the finite sum of
the iterates of its backward operator. -/
theorem truncatedBCHAction_eq_of_eq_add (k : ℕ) (g : d.truncatedGroup ℒ k)
    {a x : F.quotient k}
    (hx : x = a + F.backwardPart
      (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k)) x) :
    x = ∑ j ∈ Finset.range (k + 1),
      ((F.backwardPart (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))) ^ j) a :=
  (F.truncatedBCHAction_isAdapted d ℒ k g).eq_sum_of_eq_add hx

/-- The inverse of a truncated BCH action is the finite geometric series of its backward
operator. -/
theorem truncatedBCHAction_symm_eq_finiteRecursion (k : ℕ) (g : d.truncatedGroup ℒ k) :
    ((F.truncatedBCHAction d ℒ k g).symm : Module.End R (F.quotient k)) =
      (F.backwardPart
        (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))).finiteRecursion (k + 1) :=
  F.symm_eq_finiteRecursion _ (F.truncatedBCHAction_isAdapted d ℒ k g)

/-- The inverse of a truncated BCH action is the finite geometric series of its backward
operator, evaluated on a coefficient. -/
theorem truncatedBCHAction_symm_apply_eq_sum (k : ℕ) (g : d.truncatedGroup ℒ k)
    (a : F.quotient k) :
    (F.truncatedBCHAction d ℒ k g).symm a =
      ∑ j ∈ Finset.range (k + 1),
        ((F.backwardPart (F.truncatedBCHAction d ℒ k g : Module.End R (F.quotient k))) ^ j) a :=
  F.symm_apply_eq_sum _ (F.truncatedBCHAction_isAdapted d ℒ k g) a

end Mei.ModuleFiltration
