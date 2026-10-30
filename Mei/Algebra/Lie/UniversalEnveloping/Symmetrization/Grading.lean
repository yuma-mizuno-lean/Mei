/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Grading
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization

/-!
# Total Lie degrees of PBW averages

PBW symmetrization sends a pure symmetric tensor of homogeneous Lie elements to
its total Lie degree. Word length and Lie degree are independent here: the factors
may have distinct degrees in any additive commutative monoid. Only invertibility
of the factorial is required, without a freeness assumption on the Lie module.

We use Tau Ceti's degreewise `UniversalEnvelopingAlgebra.pbwSymmetrization`
and its permutation-average formula
(Dixmier, *Enveloping Algebras*, §2.4).
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

variable {Γ : Type*} {R : Type} {L : Type*} [AddCommMonoid Γ]
  [CommRing R] [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L)

/-- Permutation averaging retains the total Lie degree of homogeneous tensor
factors, independently of their word length and without a freeness assumption. -/
theorem pbwSymmetrization_tprod_mem_homogeneousSubmodule
    {n : ℕ} (hn : IsUnit (n.factorial : R)) (degree : Fin n → Γ)
    (x : Fin n → L) (hx : ∀ i, x i ∈ ℒ (degree i)) :
    TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization R L n hn (⨂ₛ[R] i, x i) ∈
      homogeneousSubmodule ℒ (∑ i, degree i) := by
  classical
  rw [TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_tprod]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  have hprod := SetLike.list_prod_ofFn_mem_graded (A := homogeneousSubmodule ℒ)
    (fun i => degree (σ i)) (fun i => _root_.UniversalEnvelopingAlgebra.ι R (x (σ i)))
    (fun i => ι_mem_homogeneousSubmodule ℒ (hx (σ i)))
  simpa only [List.sum_ofFn, Equiv.sum_comp] using hprod

end Mei.UniversalEnvelopingAlgebra
