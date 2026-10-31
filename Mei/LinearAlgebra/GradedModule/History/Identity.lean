/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Erasure
public import Mei.LinearAlgebra.GradedModule.History.Finite

/-!+# Identity encounters in homogeneous histories

Deleting an identity propagation map gives a bijection of surviving histories
on a homogeneous input. Its inverse repeats the incoming degree at the deleted
position. The correspondence preserves whole final decorations and selected
finite weighted sums, even when distinct histories have cancelling weights.

These coefficient identities allow encounters whose action becomes the identity
after truncation to be omitted from a propagation sequence. They do not assert
that a geometric ray avoids the omitted wall or admit a geometric reinsertion.
The homogeneous-input hypothesis matters when the deleted map is the first
operation: an identity map still decomposes a nonhomogeneous input.

We use `homogeneousHistory_removeNth`, the nonvanishing of all stages of a
surviving history, and Mathlib's `Fin.insertNth`/`Fin.removeNth` interface.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Inserting an identity map and repeating its incoming degree leaves the
whole final decoration unchanged. The input may be zero. -/
@[simp↓] -- Remove the identity before the generic history expansion runs.
theorem homogeneousHistory_insertNth_id {n : ℕ}
    (T : Fin n → Module.End R M) (r : Fin n → ι) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) :
    homogeneousHistory ℳ (j.insertNth LinearMap.id T)
      (j.insertNth (Fin.snoc (α := fun _ => ι) r p₀ j) r) a =
        homogeneousHistory ℳ T r a := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [homogeneousHistory_succ_apply, homogeneousHistory_zero,
      Fin.insertNth_apply_same, LinearMap.id_apply, Fin.snoc_zero]
    exact DirectSum.decompose_of_mem_same ℳ a.property
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.insertNth_zero', Fin.insertNth_zero', homogeneousHistory_succ_apply]
      simp only [Fin.cons_succ, Fin.cons_zero, LinearMap.id_apply]
      exact DirectSum.decompose_of_mem_same ℳ
        (homogeneousHistory_mem ℳ T r a)
    · have hT : T = Fin.cons (T 0) (fun i => T i.succ) := (Fin.cons_self_tail T).symm
      have hr : r = Fin.cons (r 0) (fun i => r i.succ) := (Fin.cons_self_tail r).symm
      rw [hT, hr, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ,
        Fin.insertNth_succ_cons, Fin.insertNth_succ_cons]
      conv_lhs => rw [homogeneousHistory_succ_apply]
      conv_rhs => rw [homogeneousHistory_succ_apply]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih]
      rfl

/-- A surviving identity encounter has equal incoming and outgoing degrees.
The statement includes the encounter next to the original homogeneous input. -/
theorem homogeneousHistory_degree_eq_of_eq_id {n : ℕ}
    (T : Fin n → Module.End R M) (r : Fin n → ι) (p₀ : ι) (a : ℳ p₀)
    (hne : homogeneousHistory ℳ T r a ≠ 0) (j : Fin n) (hj : T j = LinearMap.id) :
    r j = Fin.snoc (α := fun _ => ι) r p₀ j.succ := by
  by_contra hdeg
  apply homogeneousHistoryStage_ne_zero ℳ T r hne j.castSucc
  rw [homogeneousHistoryStage_castSucc_apply, hj, LinearMap.id_apply,
    DirectSum.decompose_of_mem_ne ℳ
      (homogeneousHistoryStage_mem_snoc ℳ T r p₀ a j.succ) (Ne.symm hdeg)]

/-- Deleting an identity encounter from a surviving history preserves its
whole final decoration. -/
theorem homogeneousHistory_removeNth_of_eq_id {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (r : Fin (n + 1) → ι)
    (p₀ : ι) (a : ℳ p₀) (hne : homogeneousHistory ℳ T r a ≠ 0)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id) :
    homogeneousHistory ℳ T r a =
      homogeneousHistory ℳ (j.removeNth T) (j.removeNth r) a := by
  apply homogeneousHistory_removeNth
  rw [homogeneousHistoryStage_castSucc_apply, hj, LinearMap.id_apply,
    homogeneousHistory_degree_eq_of_eq_id ℳ T r p₀ a hne j hj]
  exact DirectSum.decompose_of_mem_same ℳ
    (homogeneousHistoryStage_mem_snoc ℳ T r p₀ a j.succ)

/-- Removing an identity map gives exactly the surviving histories of the
shorter sequence. Reinsertion repeats the incoming degree, retaining every other
degree and the whole final decoration. No finiteness of the grading is required. -/
def homogeneousHistorySupportRemoveIdentityEquiv {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id) :
    (homogeneousHistorySupport ℳ T a : Type _) ≃
      (homogeneousHistorySupport ℳ (j.removeNth T) a : Type _) where
  toFun r := ⟨j.removeNth r.val, by
    rw [mem_homogeneousHistorySupport,
      ← homogeneousHistory_removeNth_of_eq_id ℳ T r.val p₀ a
        ((mem_homogeneousHistorySupport ..).mp r.property) j hj]
    exact (mem_homogeneousHistorySupport ..).mp r.property⟩
  invFun r := ⟨j.insertNth (Fin.snoc (α := fun _ => ι) r.val p₀ j) r.val, by
    rw [mem_homogeneousHistorySupport]
    have hT : T = j.insertNth LinearMap.id (j.removeNth T) :=
      Fin.eq_insertNth_iff.mpr ⟨hj, rfl⟩
    have he : homogeneousHistory ℳ T
        (j.insertNth (Fin.snoc (α := fun _ => ι) r.val p₀ j) r.val) a =
          homogeneousHistory ℳ (j.removeNth T) r.val a := by
      simpa only [← hT] using
        homogeneousHistory_insertNth_id ℳ (j.removeNth T) r.val p₀ a j
    rw [he]
    exact (mem_homogeneousHistorySupport ..).mp r.property⟩
  left_inv r := by
    apply Subtype.ext
    dsimp only
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨?_, rfl⟩
    rw [homogeneousHistory_degree_eq_of_eq_id ℳ T r.val p₀ a
      ((mem_homogeneousHistorySupport ..).mp r.property) j hj]
    cases j using Fin.lastCases <;>
      simp [Fin.removeNth_apply, ← Fin.castSucc_succ]
  right_inv r := by
    apply Subtype.ext
    dsimp only
    exact Fin.removeNth_insertNth ..

/-- Deletion retains the degrees at precisely the undeleted positions. -/
@[simp]
theorem homogeneousHistorySupportRemoveIdentityEquiv_val {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id)
    (r : (homogeneousHistorySupport ℳ T a : Type _)) :
    (homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a j hj r).val =
      j.removeNth r.val := (rfl)

/-- Reinsertion repeats the incoming degree at the identity encounter. -/
@[simp]
theorem homogeneousHistorySupportRemoveIdentityEquiv_symm_val {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id)
    (r : (homogeneousHistorySupport ℳ (j.removeNth T) a : Type _)) :
    ((homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a j hj).symm r).val =
      j.insertNth (Fin.snoc (α := fun _ => ι) r.val p₀ j) r.val := (rfl)

/-- The deletion bijection preserves the whole final decoration. -/
theorem homogeneousHistorySupportRemoveIdentityEquiv_decoration {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id)
    (r : (homogeneousHistorySupport ℳ T a : Type _)) :
    homogeneousHistory ℳ (j.removeNth T)
        (homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a j hj r).val a =
      homogeneousHistory ℳ T r.val a :=
  (homogeneousHistory_removeNth_of_eq_id ℳ T r.val p₀ a
    ((mem_homogeneousHistorySupport ..).mp r.property) j hj).symm

open Classical in
/-- Any selection of shortened histories has the same weighted sum before
and after deletion of an identity encounter. Distinct shortened histories remain
distinct, even when their final decorations coincide or cancel. -/
theorem sum_ite_homogeneousHistory_removeNth_of_eq_id {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (p₀ : ι) (a : ℳ p₀)
    (j : Fin (n + 1)) (hj : T j = LinearMap.id) (E : (Fin n → ι) → Prop) :
    (∑ r : (homogeneousHistorySupport ℳ T a : Type _),
      if E (j.removeNth r.val) then homogeneousHistory ℳ T r.val a else 0) =
      ∑ r : (homogeneousHistorySupport ℳ (j.removeNth T) a : Type _),
        if E r.val then homogeneousHistory ℳ (j.removeNth T) r.val a else 0 := by
  apply Fintype.sum_equiv (homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a j hj)
  intro r
  simp only [homogeneousHistorySupportRemoveIdentityEquiv_val]
  split_ifs
  · exact homogeneousHistory_removeNth_of_eq_id ℳ T r.val p₀ a
      ((mem_homogeneousHistorySupport ..).mp r.property) j hj
  · rfl

end Mei
