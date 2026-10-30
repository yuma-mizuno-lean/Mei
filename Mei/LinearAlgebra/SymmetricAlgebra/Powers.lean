/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.RingTheory.MvPolynomial.Polarization
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Algebra.Tower

/-!
# Pure powers span symmetric algebras over rational algebras

The powers of generators span each homogeneous component of a symmetric algebra
over a commutative rational algebra. Consequently linear maps out of it can be
compared on pure powers. No freeness or finite-generation hypothesis is needed.
This permits coalgebra comparisons for symmetrization to be checked on powers,
where coproducts have the binomial formula.

We transport the finite-variable polynomial polarization theorem
`TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule` along evaluation.
The universal polynomial calculation takes place over ℚ; its images span over
the given scalar ring even when that ring has zero divisors.
-/

public noncomputable section

namespace Mei.SymmetricAlgebra

open scoped BigOperators
open TauCeti.SymmetricAlgebra

variable (R M : Type*) [CommRing R] [Algebra ℚ R] [AddCommMonoid M] [Module R M]

/-- Pure powers of generators span the entire homogeneous component over any
commutative rational algebra, with no freeness assumption on the module. -/
@[simp]
theorem span_range_ι_pow (n : ℕ) :
    Submodule.span R (Set.range fun x : M => SymmetricAlgebra.ι R M x ^ n) =
      homogeneousSubmodule R M n := by
  classical
  let : Algebra ℚ (SymmetricAlgebra R M) :=
    Algebra.compHom (SymmetricAlgebra R M) (algebraMap ℚ R)
  let : IsScalarTower ℚ R (SymmetricAlgebra R M) :=
    IsScalarTower.of_algebraMap_smul fun q x =>
      (Algebra.compHom_smul_def (SymmetricAlgebra R M) (algebraMap ℚ R) q x).symm
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simpa using prod_map_ι_mem_homogeneousSubmodule R M (List.replicate n x)
  · rw [homogeneousSubmodule_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    subst n
    -- Express the universal product as a rational linear combination of powers.
    let e := MvPolynomial.aeval (R := ℚ) (fun j : Fin l.length =>
      SymmetricAlgebra.ι R M (l.get j))
    have hspan := TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule
      (K := ℚ) (σ := Fin l.length) Set.univ
      (fun q hq => MvPolynomial.funext fun x => by simpa using hq x (Set.mem_univ x))
      l.length
    have hp : (∏ j : Fin l.length, MvPolynomial.X j : MvPolynomial (Fin l.length) ℚ) ∈
        MvPolynomial.homogeneousSubmodule (Fin l.length) ℚ l.length := by
      simpa using MvPolynomial.IsHomogeneous.prod
        Finset.univ (fun j : Fin l.length => MvPolynomial.X j) (fun _ => 1)
          (fun j _ => MvPolynomial.isHomogeneous_X ℚ j)
    rw [← hspan] at hp
    -- Evaluation carries that rational span into the desired span over R.
    have he : e '' ↑(Submodule.span ℚ
        ((fun x : Fin l.length → ℚ =>
          (∑ j, x j • MvPolynomial.X (R := ℚ) j) ^ l.length) '' Set.univ))
        ⊆ (Submodule.span R
          (Set.range fun x : M => SymmetricAlgebra.ι R M x ^ l.length)).restrictScalars ℚ := by
      apply (Submodule.image_span_subset e.toLinearMap _ _).2
      intro q hq
      obtain ⟨x, _, rfl⟩ := hq
      have heq : e ((∑ j, x j • MvPolynomial.X j) ^ l.length) =
          SymmetricAlgebra.ι R M (∑ j, (algebraMap ℚ R (x j)) • l.get j) ^ l.length := by
        rw [map_pow, map_sum, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, MvPolynomial.aeval_X, map_smul]
        exact (IsScalarTower.algebraMap_smul R (x j) _).symm
      rw [AlgHom.toLinearMap_apply, heq]
      exact Submodule.subset_span (Set.mem_range_self _)
    have hep := he ⟨_, hp, rfl⟩
    simp only [e, map_prod, MvPolynomial.aeval_X] at hep
    have hprod : (List.ofFn fun j : Fin l.length => SymmetricAlgebra.ι R M (l.get j)) =
        l.map (SymmetricAlgebra.ι R M) := List.ofFn_getElem_eq_map l _
    rwa [← List.prod_ofFn, hprod] at hep

/-- Two linear maps from a symmetric algebra over a rational algebra agree
if they agree on every pure power of every generator. -/
theorem linearMap_ext_ι_pow {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : SymmetricAlgebra R M →ₗ[R] N}
    (h : ∀ x : M, ∀ n : ℕ, f (SymmetricAlgebra.ι R M x ^ n) =
      g (SymmetricAlgebra.ι R M x ^ n)) : f = g := by
  apply LinearMap.ext
  intro p
  have htop : (⊤ : Submodule R (SymmetricAlgebra R M)) ≤ LinearMap.eqLocus f g := by
    rw [← iSup_homogeneousSubmodule_eq_top R M]
    refine iSup_le fun n => ?_
    rw [← span_range_ι_pow R M n]
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact h x n)
  exact htop Submodule.mem_top

end Mei.SymmetricAlgebra
