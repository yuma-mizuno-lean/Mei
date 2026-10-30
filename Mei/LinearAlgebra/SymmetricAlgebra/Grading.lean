/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# The symmetric algebra of a graded module

A decomposition of a module induces a grading on its symmetric algebra by total
module degree. The homogeneous pieces are spans of products of homogeneous
generators. The grading monoid is arbitrary; in particular this retains lattice
degrees independently of the usual grading by word length. No basis or flatness
hypothesis is needed, and the scalar ring may be a commutative semiring.

This supplies the symmetric-algebra side of graded PBW comparisons. The construction
uses the universal property of `SymmetricAlgebra.lift` and follows the direct-sum
construction of `Mei.UniversalEnvelopingAlgebra.gradedAlgebra`. The pure symmetric
tensor formula uses Tau Ceti's `SymmetricPower.toSymmetricAlgebra`; that formula
inherits its requirement that the scalar semiring lie in `Type`.
-/

public section

namespace Mei.SymmetricAlgebra

open _root_.SymmetricAlgebra
open scoped DirectSum

variable {Γ R M : Type*} [AddCommMonoid Γ] [CommSemiring R]
  [AddCommMonoid M] [Module R M] (ℳ : Γ → Submodule R M)

local notation "S" => _root_.SymmetricAlgebra R M

/-- Products of homogeneous module elements, spanning the total module degree `n`. -/
def homogeneousSubmodule (n : Γ) : Submodule R S :=
  Submodule.span R {a | ∃ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n ∧
    (l.map (fun x => ι R M (x.2 : M))).prod = a}

/-- The word-span description of a module-degree component. -/
theorem homogeneousSubmodule_def (n : Γ) :
    homogeneousSubmodule ℳ n =
      Submodule.span R {a | ∃ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n ∧
        (l.map (fun x => ι R M (x.2 : M))).prod = a} := (rfl)

/-- To contain a component, it suffices to contain its homogeneous words. -/
theorem homogeneousSubmodule_le_iff (n : Γ) (P : Submodule R S) :
    homogeneousSubmodule ℳ n ≤ P ↔
      ∀ l : List (Σ i, ℳ i), (l.map Sigma.fst).sum = n →
        (l.map (fun x => ι R M (x.2 : M))).prod ∈ P := by
  rw [homogeneousSubmodule_def, Submodule.span_le]
  constructor
  · intro h l hl
    exact h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- A homogeneous word belongs to the component given by its total module degree. -/
theorem prod_mem_homogeneousSubmodule (l : List (Σ i, ℳ i)) :
    (l.map (fun x => ι R M (x.2 : M))).prod ∈
      homogeneousSubmodule ℳ (l.map Sigma.fst).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- A module generator retains its degree in the symmetric algebra. -/
theorem ι_mem_homogeneousSubmodule {n : Γ} {x : M} (hx : x ∈ ℳ n) :
    ι R M x ∈ homogeneousSubmodule ℳ n := by
  simpa using prod_mem_homogeneousSubmodule ℳ [⟨n, x, hx⟩]

/-- Multiplication adds total module degrees. -/
instance homogeneousSubmodule_gradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule ℳ) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro m n a b ha hb
    have hmul : homogeneousSubmodule ℳ m * homogeneousSubmodule ℳ n ≤
        homogeneousSubmodule ℳ (m + n) := by
      rw [homogeneousSubmodule_def, homogeneousSubmodule_def,
        Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      simpa [hl, ht] using prod_mem_homogeneousSubmodule ℳ (l ++ t)
    exact hmul (Submodule.mul_mem_mul ha hb)

variable [DecidableEq Γ] [DirectSum.Decomposition ℳ]

private noncomputable def gradedι : M →ₗ[R] ⨁ n, homogeneousSubmodule ℳ n :=
  (DirectSum.lmap fun n =>
    (((ι R M).comp (ℳ n).subtype).codRestrict _
      fun x => ι_mem_homogeneousSubmodule ℳ x.property)).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem gradedι_apply {n : Γ} (x : ℳ n) :
    gradedι ℳ x = DirectSum.of (fun n => ↥(homogeneousSubmodule ℳ n)) n
      ⟨ι R M (x : M), ι_mem_homogeneousSubmodule ℳ x.property⟩ := by
  simp only [gradedι, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe, DirectSum.lmap_of]
  rfl

private noncomputable def decomposeAlgHom : S →ₐ[R] ⨁ n, homogeneousSubmodule ℳ n :=
  lift (gradedι ℳ)

private theorem decomposeAlgHom_ι {n : Γ} (x : ℳ n) :
    decomposeAlgHom ℳ (ι R M (x : M)) =
      DirectSum.of (fun n => ↥(homogeneousSubmodule ℳ n)) n
        ⟨ι R M (x : M), ι_mem_homogeneousSubmodule ℳ x.property⟩ := by
  rw [decomposeAlgHom, lift_ι_apply, gradedι_apply]

private theorem coeAlgHom_comp_decomposeAlgHom :
    (DirectSum.coeAlgHom (homogeneousSubmodule ℳ)).comp (decomposeAlgHom ℳ) =
      AlgHom.id R S := by
  apply _root_.SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | homogeneous x =>
    exact (congrArg (DirectSum.coeAlgHom (homogeneousSubmodule ℳ))
      (decomposeAlgHom_ι ℳ x)).trans (DirectSum.coeAlgHom_of _ _ _)

private theorem decomposeAlgHom_prod (l : List (Σ i, ℳ i)) :
    decomposeAlgHom ℳ (l.map (fun x => ι R M (x.2 : M))).prod =
      DirectSum.of (fun n => ↥(homogeneousSubmodule ℳ n)) (l.map Sigma.fst).sum
        ⟨(l.map (fun x => ι R M (x.2 : M))).prod, prod_mem_homogeneousSubmodule ℳ l⟩ := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, DirectSum.one_def]; rfl
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, decomposeAlgHom_ι, ih,
      DirectSum.of_mul_of]
    congr 1

private theorem decomposeAlgHom_apply (n : Γ) (x : homogeneousSubmodule ℳ n) :
    decomposeAlgHom ℳ (x : S) =
      DirectSum.of (fun n => ↥(homogeneousSubmodule ℳ n)) n x := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    subst n
    exact decomposeAlgHom_prod ℳ l
  | zero =>
    rw [map_zero]
    exact (map_zero (DirectSum.of (fun n => ↥(homogeneousSubmodule ℳ n)) n)).symm
  | add x y hx hy hxi hyi =>
    rw [map_add, hxi, hyi, ← map_add]
    rfl
  | smul r x hx hxi =>
    rw [map_smul, hxi, ← DirectSum.of_smul]
    rfl

/-- The symmetric algebra of a decomposed module is graded by total module degree,
without freeness or flatness assumptions. -/
@[no_expose]
noncomputable instance gradedAlgebra : GradedAlgebra (homogeneousSubmodule ℳ) := by
  apply GradedAlgebra.ofAlgHom _ (decomposeAlgHom ℳ)
  · exact coeAlgHom_comp_decomposeAlgHom ℳ
  · exact decomposeAlgHom_apply ℳ

/-- Inclusion into the symmetric algebra commutes with homogeneous projections. -/
theorem ι_component (x : M) (n : Γ) :
    ι R M (DirectSum.decompose ℳ x n : M) =
      (DirectSum.decompose (homogeneousSubmodule ℳ) (ι R M x) n : S) :=
  DirectSum.map_decompose_shift ℳ (homogeneousSubmodule ℳ)
    (ι R M).toAddMonoidHom id Function.injective_id
    (fun _ _ hx => ι_mem_homogeneousSubmodule ℳ hx) n x

end Mei.SymmetricAlgebra

namespace Mei.SymmetricAlgebra

open scoped TensorProduct

variable {Γ : Type*} {R : Type} {M : Type*} [AddCommMonoid Γ]
  [CommSemiring R] [AddCommMonoid M] [Module R M] (ℳ : Γ → Submodule R M)

/-- Multiplication of a pure symmetric tensor retains the total degree of its
homogeneous factors in the symmetric algebra. -/
theorem toSymmetricAlgebra_tprod_mem_homogeneousSubmodule
    {n : ℕ} (degree : Fin n → Γ) (x : Fin n → M) (hx : ∀ i, x i ∈ ℳ (degree i)) :
    TauCeti.SymmetricPower.toSymmetricAlgebra R M n (⨂ₛ[R] i, x i) ∈
      homogeneousSubmodule ℳ (∑ i, degree i) := by
  rw [TauCeti.SymmetricPower.toSymmetricAlgebra_tprod]
  exact SetLike.prod_mem_graded _ _ _ fun i _ =>
    ι_mem_homogeneousSubmodule ℳ (hx i)

end Mei.SymmetricAlgebra
