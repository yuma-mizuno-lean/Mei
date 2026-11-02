/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.End.Recursion
public import Mei.LinearAlgebra.ModuleFiltration.Completion
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent endomorphisms on finite filtered quotients

An endomorphism raising a module filtration by one induces an endomorphism on
each finite quotient. Its `(k + 1)`st power vanishes on the order-`k` quotient.
The original endomorphism need not be nilpotent. No separatedness, completeness,
finiteness, or characteristic-zero hypothesis is used.

These compatible nilpotent endomorphisms turn power series into finite sums at
each order, so evaluations can be assembled across the quotient tower. In particular,
filtration-raising Lie actions use this construction for their finite-order
representations before exponentiation.

When the filtration itself has finite length, an endomorphism raising it is
nilpotent on the whole module, not only at each order. The recursion `x = a + f x`
is then solved by the shared semimodule theorem `Module.End.finiteRecursion`, so no
second existence or uniqueness argument is needed for this case.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (f : Module.End R M)
  (hf : ∀ k, F.submodule k ≤ (F.submodule (k + 1)).comap f)

/-- A filtration-raising endomorphism induces an endomorphism at each finite order. -/
def quotientRaisingEnd (k : ℕ) : Module.End R (F.quotient k) :=
  (F.submodule (k + 1)).mapQ (F.submodule (k + 1)) f
    (fun _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx))

/-- The finite endomorphism is the standard quotient map of the original endomorphism. -/
theorem quotientRaisingEnd_eq_mapQ (k : ℕ) :
    F.quotientRaisingEnd f hf k =
      (F.submodule (k + 1)).mapQ (F.submodule (k + 1)) f
        (fun _ hx => F.antitone (Nat.le_succ (k + 1)) (hf (k + 1) hx)) := (rfl)

/-- On a representative, the finite endomorphism applies the original endomorphism. -/
@[simp]
theorem quotientRaisingEnd_mk (k : ℕ) (x : M) :
    F.quotientRaisingEnd f hf k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  Submodule.mapQ_apply _ _ _ x

/-- Every power of the finite endomorphism is induced by the corresponding original power. -/
@[simp]
theorem quotientRaisingEnd_pow_mk (k n : ℕ) (x : M) :
    (F.quotientRaisingEnd f hf k ^ n) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((f ^ n) x) := by
  rw [quotientRaisingEnd_eq_mapQ, ← Submodule.mapQ_pow, Submodule.mapQ_apply]

/-- On the order-`k` quotient, the `(k + 1)`st power vanishes. -/
@[simp]
theorem quotientRaisingEnd_pow_eq_zero (k : ℕ) :
    F.quotientRaisingEnd f hf k ^ (k + 1) = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨x, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective a
  rw [Submodule.mkQ_apply, quotientRaisingEnd_pow_mk, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  have h := Module.End.pow_apply_mem_of_map_le (T := f) (F := F.submodule)
    (fun n => by rintro _ ⟨y, hy, rfl⟩; exact hf n hy)
    (by simp : x ∈ F.submodule 0) (k + 1)
  simpa only [Nat.zero_add] using h

/-- Every induced finite endomorphism is nilpotent. -/
theorem isNilpotent_quotientRaisingEnd (k : ℕ) : IsNilpotent (F.quotientRaisingEnd f hf k) :=
  ⟨k + 1, F.quotientRaisingEnd_pow_eq_zero f hf k⟩

/-- The quotient endomorphisms commute with all transition maps. -/
@[simp]
theorem transition_quotientRaisingEnd {k l : ℕ} (hkl : k ≤ l) (x : F.quotient l) :
    F.transition hkl (F.quotientRaisingEnd f hf l x) =
      F.quotientRaisingEnd f hf k (F.transition hkl x) := by
  obtain ⟨a, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp

include hf in
/-- A raising endomorphism of a filtration that vanishes at order `r` is nilpotent. -/
theorem pow_eq_zero_of_submodule_eq_bot (hr : F.submodule r = ⊥) : f ^ r = 0 := by
  apply LinearMap.ext
  intro x
  have h := Module.End.pow_apply_mem_of_map_le (T := f) (F := F.submodule)
    (fun n => by rintro _ ⟨y, hy, rfl⟩; exact hf n hy)
    (show x ∈ F.submodule 0 by simp) r
  rw [Nat.zero_add, hr] at h
  simpa only [LinearMap.zero_apply, Submodule.mem_bot] using h

include hf in
/-- The shared semimodule recursion solves the recursion of a raising endomorphism
of a finite-length filtration. -/
theorem eq_finiteRecursion_of_submodule_eq_bot (hr : F.submodule r = ⊥) {a x : M}
    (hx : x = a + f x) : x = f.finiteRecursion r a :=
  Module.End.eq_finiteRecursion_of_eq_add f (F.pow_eq_zero_of_submodule_eq_bot f hf hr) hx

include hf in
/-- Two solutions of the recursion agree, for a raising endomorphism of a
finite-length filtration. -/
theorem eq_of_eq_add_of_submodule_eq_bot (hr : F.submodule r = ⊥) {a x y : M}
    (hx : x = a + f x) (hy : y = a + f y) : x = y :=
  Module.End.eq_of_eq_add_of_pow_eq_zero f (F.pow_eq_zero_of_submodule_eq_bot f hf hr) hx hy

include hf in
/-- The recursion of a raising endomorphism of a finite-length filtration has a
unique solution. -/
theorem existsUnique_eq_add_of_submodule_eq_bot (hr : F.submodule r = ⊥) (a : M) :
    ∃! x, x = a + f x :=
  Module.End.existsUnique_eq_add_of_pow_eq_zero f (F.pow_eq_zero_of_submodule_eq_bot f hf hr) a

end Mei.ModuleFiltration
