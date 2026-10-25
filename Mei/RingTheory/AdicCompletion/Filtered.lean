/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Algebra
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Ideal-adic and filtered completions

The completion of the ideal-power filtration agrees with Mathlib's adic
completion. The filtered completion records quotients by `I^(k+1)`, while the
adic completion also records the trivial quotient by `I^0`. The comparison
forgets this redundant coordinate and commutes with the canonical maps.

The construction uses `AdicCompletion.evalₐ`, `AdicCompletion.liftAlgHom` and
the compatible-family universal property `Mei.AlgFiltration.liftₐ`.
-/

public section

noncomputable section

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Adic projections commute with the canonical maps between ideal-power quotients. -/
theorem factor_evalₐ {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (evalₐ I n x) = evalₐ I m x := by
  rw [← factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _)),
    ← factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval I A n x)
  have hx := transitionMap_comp_eval_apply I A h x
  rw [← eval_apply] at hx
  rw [← ha, transitionMap_ideal_mk] at hx
  rw [← eval_apply] at hx
  rw [← hx, ← ha]
  simp

end AdicCompletion

namespace Mei.AlgFiltration

variable {A : Type*} [CommRing A] (I : Ideal A)

local notation "Q" n => Ideal.quotientEquivAlgOfEq A (ofIdeal_ideal I n)

private def fromAdicCompletion :
    AdicCompletion I A →ₐ[A] (ofIdeal I).completion :=
  (ofIdeal I).liftₐ (fun k => ((Q (k + 1)).symm.toAlgHom).comp (AdicCompletion.evalₐ I (k + 1))) (by
    intro k l h
    ext x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [← AdicCompletion.factor_evalₐ I (Nat.add_le_add_right h 1) x]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (l + 1) x)
    rw [← ha]
    simp)

private theorem projection_fromAdicCompletion (k : ℕ) (x : AdicCompletion I A) :
    (ofIdeal I).projection k (fromAdicCompletion I x) =
      (Q (k + 1)).symm (AdicCompletion.evalₐ I (k + 1) x) := by
  simp only [fromAdicCompletion, projection_liftₐ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

private def adicComponent (n : ℕ) : (ofIdeal I).completion →ₐ[A] A ⧸ I ^ n :=
  (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
    (((Q (n + 1)).toAlgHom).comp ((ofIdeal I).projectionₐ n))

private theorem adicComponent_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp (adicComponent I n) =
      adicComponent I m := by
  ext x
  simp only [adicComponent, AlgHom.comp_apply, projectionₐ_apply, AlgEquiv.coe_toAlgHom]
  rw [← (ofIdeal I).factor_projection h x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((ofIdeal I).projection n x)
  rw [← ha]
  simp

private def toAdicCompletion :
    (ofIdeal I).completion →ₐ[A] AdicCompletion I A :=
  AdicCompletion.liftAlgHom I (adicComponent I) (adicComponent_compatible I)

private theorem eval_toAdicCompletion (n : ℕ) (x : (ofIdeal I).completion) :
    AdicCompletion.evalₐ I n (toAdicCompletion I x) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
        ((Q (n + 1)) ((ofIdeal I).projection n x)) := by
  rw [toAdicCompletion,
    AdicCompletion.evalₐ_liftAlgHom I (adicComponent I) (adicComponent_compatible I)]
  simp only [adicComponent, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    projectionₐ_apply, Ideal.Quotient.factorₐ_apply]

/-- The adic completion is the completion of the ideal-power filtration, with
its redundant order-zero quotient omitted. -/
def adicCompletionEquiv : AdicCompletion I A ≃ₐ[A] (ofIdeal I).completion where
  toFun := fromAdicCompletion I
  map_mul' := (fromAdicCompletion I).map_mul
  map_add' := (fromAdicCompletion I).map_add
  commutes' := (fromAdicCompletion I).commutes
  invFun := toAdicCompletion I
  left_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [eval_toAdicCompletion, projection_fromAdicCompletion,
      AlgEquiv.apply_symm_apply, AdicCompletion.factor_evalₐ I (Nat.le_succ n)]
  right_inv x := by
    apply (ofIdeal I).completion_ext
    intro k
    rw [projection_fromAdicCompletion, eval_toAdicCompletion]
    rw [← (ofIdeal I).factor_projection (Nat.le_succ k) x]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((ofIdeal I).projection (k + 1) x)
    rw [← ha]
    simp

/-- The comparison sends the adic quotient of order `k+1` to filtered order `k`. -/
@[simp]
theorem projection_adicCompletionEquiv (k : ℕ) (x : AdicCompletion I A) :
    (ofIdeal I).projection k (adicCompletionEquiv I x) =
      (Q (k + 1)).symm (AdicCompletion.evalₐ I (k + 1) x) :=
  projection_fromAdicCompletion I k x

/-- The inverse comparison recovers every positive-order adic projection. -/
@[simp]
theorem eval_adicCompletionEquiv_symm (k : ℕ) (x : (ofIdeal I).completion) :
    AdicCompletion.evalₐ I (k + 1) ((adicCompletionEquiv I).symm x) =
      (Q (k + 1)) ((ofIdeal I).projection k x) := by
  apply (Q (k + 1)).symm.injective
  rw [← projection_adicCompletionEquiv, AlgEquiv.apply_symm_apply,
    AlgEquiv.symm_apply_apply]

/-- The comparison preserves the canonical image of the original ring. -/
@[simp]
theorem adicCompletionEquiv_of (a : A) :
    adicCompletionEquiv I (AdicCompletion.of I A a) = (ofIdeal I).toCompletion a := by
  apply (ofIdeal I).completion_ext
  intro k
  simp

end Mei.AlgFiltration
