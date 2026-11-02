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

When the filtration itself vanishes at a finite order, the original endomorphism
is globally nilpotent (`pow_eq_zero_of_submodule_eq_bot`), and the shared
semimodule recursion `Module.End.finiteRecursion` then supplies solutions and
uniqueness for `x = a + f x` on the module itself
(`eq_finiteRecursion_of_submodule_eq_bot` and its consequences).

These compatible nilpotent endomorphisms turn power series into finite sums at
each order, so evaluations can be assembled across the quotient tower. In particular,
filtration-raising Lie actions use this construction for their finite-order
representations before exponentiation.
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

include hf in
/-- A filtration that vanishes at order `r` makes a filtration-raising
endomorphism globally nilpotent: the `r`-th power vanishes on the whole module,
not only on a quotient. No separatedness, completeness or finiteness hypothesis
is used beyond the raising hypothesis itself. -/
theorem pow_eq_zero_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥) :
    f ^ r = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  have h := Module.End.pow_apply_mem_of_map_le (T := f) (F := F.submodule)
    (fun n => by rintro _ ⟨y, hy, rfl⟩; exact hf n hy)
    (by simp : x ∈ F.submodule 0) r
  rw [Nat.zero_add, hr] at h
  exact (Submodule.mem_bot R).mp h

include hf in
/-- A finite-length filtration makes a filtration-raising endomorphism nilpotent
on the original module. -/
theorem isNilpotent_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥) :
    IsNilpotent f :=
  ⟨r, F.pow_eq_zero_of_submodule_eq_bot f hf hr⟩

include hf in
/-- With a finite-length filtration, the recursion `x = a + f x` on the module
itself is solved by the shared finite geometric sum; the proof applies that
shared solution to the global nilpotence above and carries no second expansion
argument. -/
theorem eq_finiteRecursion_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥)
    {a x : M} (hx : x = a + f x) :
    x = f.finiteRecursion r a :=
  f.eq_finiteRecursion_of_eq_add (F.pow_eq_zero_of_submodule_eq_bot f hf hr) hx

include hf in
/-- With a finite-length filtration, two solutions of the same filtration-recursion
agree. -/
theorem eq_of_eq_add_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥)
    {a x y : M} (hx : x = a + f x) (hy : y = a + f y) :
    x = y :=
  f.eq_of_eq_add_of_pow_eq_zero (F.pow_eq_zero_of_submodule_eq_bot f hf hr) hx hy

include hf in
/-- With a finite-length filtration, the filtration-recursion `x = a + f x` has
exactly one solution. -/
theorem existsUnique_eq_add_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥)
    (a : M) :
    ∃! x : M, x = a + f x :=
  f.existsUnique_eq_add_of_pow_eq_zero (F.pow_eq_zero_of_submodule_eq_bot f hf hr) a

/-- The quotient endomorphisms commute with all transition maps. -/
@[simp]
theorem transition_quotientRaisingEnd {k l : ℕ} (hkl : k ≤ l) (x : F.quotient l) :
    F.transition hkl (F.quotientRaisingEnd f hf l x) =
      F.quotientRaisingEnd f hf k (F.transition hkl x) := by
  obtain ⟨a, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp

/-- A filtered coefficient intertwiner commutes with the induced raising maps,
allowing independently chosen cutoff orders and only a bound at those orders. -/
theorem mapQ_quotientRaisingEnd {N : Type*} [AddCommGroup N] [Module R N]
    (G : ModuleFiltration R N) (g : Module.End R N)
    (hg : ∀ k, G.submodule k ≤ (G.submodule (k + 1)).comap g)
    (r : M →ₗ[R] N) (l k : ℕ)
    (hr : F.submodule (l + 1) ≤ (G.submodule (k + 1)).comap r)
    (hfg : r.comp f = g.comp r) (x : F.quotient l) :
    (F.submodule (l + 1)).mapQ (G.submodule (k + 1)) r hr
        (F.quotientRaisingEnd f hf l x) =
      G.quotientRaisingEnd g hg k
        ((F.submodule (l + 1)).mapQ (G.submodule (k + 1)) r hr x) := by
  obtain ⟨a, rfl⟩ := (F.submodule (l + 1)).mkQ_surjective x
  simp only [Submodule.mkQ_apply, quotientRaisingEnd_mk, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hfg a)

end Mei.ModuleFiltration
