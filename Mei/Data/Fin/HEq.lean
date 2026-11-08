/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Heterogeneous equality for singleton-indexed functions

Functions indexed by singleton types are determined by their value at the initial index. These
lemmas extend this observation to functions whose domains use two provably zero length parameters,
including dependent functions whose initial values form a heterogeneous sigma pair.
-/

public section

namespace Fin

universe uV uW uX

/-- Two functions on provably singleton finite types are heterogeneously equal when their values at
index zero agree. -/
theorem zero_index_heq {n m : ℕ} (hn : n = 0) (hm : m = 0)
    {A : Type uV} (f : Fin (n + 1) → A) (g : Fin (m + 1) → A)
    (h : f 0 = g 0) : HEq f g := by
  subst n
  subst m
  exact heq_of_eq (funext fun j => by
    rw [Fin.fin_one_eq_zero j]
    exact h)

/-- Two dependent functions and their decorated values on provably singleton finite types are
heterogeneously equal when their index functions agree and their initial decorated values agree as
sigma pairs. -/
theorem zero_index_dep_heq {S : Type uV} {A : S → Type uW} {B : ∀ s, A s → Type uX}
    {n m : ℕ} (hn : n = 0) (hm : m = 0)
    {st : Fin (n + 1) → S} {st' : Fin (m + 1) → S} (hst : HEq st st')
    {f : ∀ j, A (st j)} {g : ∀ j, A (st' j)}
    {df : ∀ j, B (st j) (f j)} {dg : ∀ j, B (st' j) (g j)}
    (h : HEq (⟨f 0, df 0⟩ : Σ a, B (st 0) a) (⟨g 0, dg 0⟩ : Σ a, B (st' 0) a)) :
    HEq f g ∧ HEq df dg := by
  subst n
  subst m
  have hst' : st = st' := eq_of_heq hst
  subst st'
  have h' : (⟨f 0, df 0⟩ : Σ a, B (st 0) a) = ⟨g 0, dg 0⟩ := eq_of_heq h
  have hfg : f = g := funext fun j => by
    rw [Fin.fin_one_eq_zero j]
    exact (Sigma.mk.inj h').1
  subst g
  exact ⟨HEq.rfl, heq_of_eq (funext fun j => by
    rw [Fin.fin_one_eq_zero j]
    exact eq_of_heq (Sigma.mk.inj h').2)⟩

end Fin
