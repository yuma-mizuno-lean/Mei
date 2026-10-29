/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.MonoidAlgebra.Filtration

/-!
# Weighted coefficient maps of monoid algebras

A coefficient map and a multiplicative weight send `r z^m` to
`φ(r) χ(m) z^m`. Such maps preserve every allowed-increment monomial ideal,
even when coefficients or weights vanish. They therefore give continuous maps
for monomial completions without an injectivity assumption.

The construction uses Mathlib's `AddMonoidAlgebra.liftNCAlgHom`; the filtration
bound uses the generator characterization of `AddSubmonoid.monoidAlgebraIdeal`.
-/

public section
noncomputable section

namespace AddMonoidAlgebra

variable {K R S M : Type*} [CommSemiring K] [Semiring R] [CommSemiring S]
  [Algebra K R] [Algebra K S] [AddCommMonoid M]

/-- Change coefficients and weight each exponent multiplicatively. -/
def weightedMap (φ : R →ₐ[K] S) (χ : Multiplicative M →* S) : R[M] →ₐ[K] S[M] :=
  liftNCAlgHom (singleZeroAlgHom.comp φ)
    { toFun m := single m.toAdd (χ m)
      map_one' := by simp [one_def]
      map_mul' m n := by simp [single_mul_single] }
    (fun _ _ => Commute.all _ _)

/-- The characteristic monomial equation for a weighted map. -/
@[simp]
theorem weightedMap_single (φ : R →ₐ[K] S) (χ : Multiplicative M →* S) (m : M) (r : R) :
    weightedMap φ χ (single m r) = single m (φ r * χ (.ofAdd m)) := by
  simp [weightedMap, liftNC_single, single_mul_single]

/-- Identity coefficients and unit weights give the identity map. -/
@[simp]
theorem weightedMap_id {R : Type*} [CommSemiring R] [Algebra K R] :
    weightedMap (AlgHom.id K R) (1 : Multiplicative M →* R) = AlgHom.id K R[M] := by
  apply AlgHom.ext
  intro a
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp_all
  | single m r => simp

/-- Successive weighted maps multiply weights after transporting coefficients. -/
@[simp]
theorem weightedMap_comp {T : Type*} [CommSemiring T] [Algebra K T]
    (φ : R →ₐ[K] S) (χ : Multiplicative M →* S)
    (ψ : S →ₐ[K] T) (ω : Multiplicative M →* T) :
    (weightedMap ψ ω).comp (weightedMap φ χ) =
      weightedMap (ψ.comp φ) (ω * ψ.toMonoidHom.comp χ) := by
  apply AlgHom.ext
  intro a
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp_all
  | single m r => simp [mul_comm, mul_assoc]

end AddMonoidAlgebra

namespace AddSubmonoid

variable {K R S M : Type*} [CommSemiring K] [Semiring R] [CommSemiring S]
  [Algebra K R] [Algebra K S] [AddCommMonoid M]

/-- Weighted coefficient maps preserve every allowed-increment monomial ideal. -/
theorem monoidAlgebraIdeal_le_comap_weightedMap (P : AddSubmonoid M) (δ : M →+ ℤ)
    (φ : R →ₐ[K] S) (χ : Multiplicative M →* S) (k : ℕ) :
    P.monoidAlgebraIdeal δ k ≤
      (P.monoidAlgebraIdeal δ k).comap (AddMonoidAlgebra.weightedMap φ χ) := by
  rw [monoidAlgebraIdeal_le_iff]
  intro n hn hd
  simp only [Ideal.mem_comap, AddMonoidAlgebra.of'_apply,
    AddMonoidAlgebra.weightedMap_single, map_one, one_mul,
    single_mem_monoidAlgebraIdeal_iff]
  exact Or.inr ⟨n, hn, hd, 0, by simp⟩

end AddSubmonoid
