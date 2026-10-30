/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Grading
public import Mei.Algebra.Lie.UniversalEnveloping.Symmetrization.Basic
public import Mei.LinearAlgebra.SymmetricAlgebra.Grading

/-!
# Total Lie degrees of PBW averages

PBW symmetrization sends a pure symmetric tensor of homogeneous Lie elements to
its total Lie degree. Word length and Lie degree are independent here: the factors
may have distinct degrees in any additive commutative monoid. Only invertibility
of the factorial is required, without a freeness assumption on the Lie module.

Over a commutative rational algebra, the global symmetrization map preserves
these components, commutes with homogeneous projections, and maps each symmetric
component onto the corresponding enveloping component. These statements retain
the lattice grading in addition to the independent PBW word filtration.

We use Tau Ceti's degreewise `UniversalEnvelopingAlgebra.pbwSymmetrization`
and its permutation-average formula
(Dixmier, *Enveloping Algebras*, §2.4).
The global comparison uses `Mei.UniversalEnvelopingAlgebra.pbwSymmetrization`,
its surjectivity, and the induced grading of `Mei.SymmetricAlgebra`.
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

variable [Algebra ℚ R]

/-- Global PBW symmetrization preserves total Lie degree, without requiring a
direct-sum decomposition or freeness of the homogeneous modules. -/
theorem pbwSymmetrization_mem_homogeneousSubmodule {n : Γ}
    {p : _root_.SymmetricAlgebra R L}
    (hp : p ∈ Mei.SymmetricAlgebra.homogeneousSubmodule ℒ n) :
    pbwSymmetrization R L p ∈ homogeneousSubmodule ℒ n := by
  have hle : Mei.SymmetricAlgebra.homogeneousSubmodule ℒ n ≤
      (homogeneousSubmodule ℒ n).comap (pbwSymmetrization R L) := by
    rw [Mei.SymmetricAlgebra.homogeneousSubmodule_le_iff]
    intro l hl
    have h := pbwSymmetrization_tprod_mem_homogeneousSubmodule ℒ
      (IsUnit.natCast_factorial_of_algebra ℚ l.length)
      (fun i => (l.get i).1) (fun i => ((l.get i).2 : L))
      (fun i => (l.get i).2.property)
    rw [← pbwSymmetrization_toSymmetricAlgebra,
      TauCeti.SymmetricPower.toSymmetricAlgebra_tprod] at h
    simp only [← List.prod_ofFn, ← List.sum_ofFn, List.get_eq_getElem] at h
    rw [List.ofFn_getElem_eq_map l (fun x => _root_.SymmetricAlgebra.ι R L (x.2 : L)),
      List.ofFn_getElem_eq_map l Sigma.fst, hl] at h
    exact h
  exact hle hp

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- PBW symmetrization commutes with homogeneous projections for the original
Lie grading, independently of word length. -/
@[simp↓] -- Commute the projection before expanding its input into sums or products.
theorem pbwSymmetrization_component (p : _root_.SymmetricAlgebra R L) (n : Γ) :
    pbwSymmetrization R L
        (DirectSum.decompose (Mei.SymmetricAlgebra.homogeneousSubmodule ℒ) p n :
          _root_.SymmetricAlgebra R L) =
      (DirectSum.decompose (homogeneousSubmodule ℒ) (pbwSymmetrization R L p) n :
        _root_.UniversalEnvelopingAlgebra R L) :=
  DirectSum.map_decompose_shift (Mei.SymmetricAlgebra.homogeneousSubmodule ℒ)
    (homogeneousSubmodule ℒ) (pbwSymmetrization R L).toAddMonoidHom
    id Function.injective_id (fun _ _ hp => pbwSymmetrization_mem_homogeneousSubmodule ℒ hp)
    n p

/-- A homogeneous enveloping element has a symmetric preimage of exactly the
same Lie degree, even when the Lie algebra is not free. -/
theorem exists_pbwSymmetrization_eq_of_mem_homogeneousSubmodule {n : Γ}
    {a : _root_.UniversalEnvelopingAlgebra R L} (ha : a ∈ homogeneousSubmodule ℒ n) :
    ∃ p ∈ Mei.SymmetricAlgebra.homogeneousSubmodule ℒ n, pbwSymmetrization R L p = a := by
  obtain ⟨p, hp⟩ := pbwSymmetrization_surjective R L a
  refine ⟨DirectSum.decompose (Mei.SymmetricAlgebra.homogeneousSubmodule ℒ) p n,
    (DirectSum.decompose (Mei.SymmetricAlgebra.homogeneousSubmodule ℒ) p n).property, ?_⟩
  rw [pbwSymmetrization_component, hp, DirectSum.decompose_of_mem_same _ ha]

/-- Symmetrization maps each symmetric Lie-degree component onto the entire
enveloping component of that degree. -/
@[simp]
theorem map_homogeneousSubmodule_pbwSymmetrization (n : Γ) :
    (Mei.SymmetricAlgebra.homogeneousSubmodule ℒ n).map (pbwSymmetrization R L) =
      homogeneousSubmodule ℒ n := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact pbwSymmetrization_mem_homogeneousSubmodule ℒ hp
  · intro a ha
    exact exists_pbwSymmetrization_eq_of_mem_homogeneousSubmodule ℒ ha

end Mei.UniversalEnvelopingAlgebra
