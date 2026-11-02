/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

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
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (F : ModuleFiltration R M) (f : Module.End R M)
  (hf : F.RaisesFiltration f)

/-- A filtration-raising endomorphism induces an endomorphism at each finite order. -/
def quotientRaisingEnd (k : ℕ) : Module.End R (F.quotient k) :=
  (F.submodule (k + 1)).mapQ (F.submodule (k + 1)) f
    (fun _ hx => F.antitone (Nat.le_succ (k + 1)) (RaisesFiltration.map_mem hf hx))

/-- The finite endomorphism is the standard quotient map of the original endomorphism. -/
theorem quotientRaisingEnd_eq_mapQ (k : ℕ) :
    F.quotientRaisingEnd f hf k =
      (F.submodule (k + 1)).mapQ (F.submodule (k + 1)) f
        (fun _ hx => F.antitone (Nat.le_succ (k + 1)) (RaisesFiltration.map_mem hf hx)) := (rfl)

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
    (fun n => by rintro _ ⟨y, hy, rfl⟩; exact RaisesFiltration.map_mem hf hy)
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

end Mei.ModuleFiltration
