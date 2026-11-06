/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.Component
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear families with finite homogeneous support

For a decomposed module, `GradedOperators ℳ H` consists of linear maps from `H`
whose homogeneous support is uniformly finite on the entire input module.
It is the image of the direct sum of maps into the homogeneous pieces.
Evaluation is injective jointly over all inputs and respects homogeneous components.
The input module need not be finitely generated, and the grading need not be finite.

The construction uses `DirectSum.toModule`, `LinearEquiv.ofInjective` and the
restriction of a direct-sum decomposition along a linear equivalence.
-/

public noncomputable section

open scoped DirectSum

namespace Mei

variable {R H M ι : Type*} [CommSemiring R] [AddCommMonoid H] [Module R H]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Assemble a finitely supported family of homogeneous linear maps. -/
def gradedOperatorMap : (⨁ q, H →ₗ[R] ℳ q) →ₗ[R] (H →ₗ[R] M) :=
  DirectSum.toModule R ι (H →ₗ[R] M)
    (fun q => LinearMap.llcomp R H (ℳ q) M (ℳ q).subtype)

omit [DirectSum.Decomposition ℳ] in
@[simp]
theorem gradedOperatorMap_lof (q : ι) (f : H →ₗ[R] ℳ q) :
    gradedOperatorMap ℳ (DirectSum.lof R ι (fun q => H →ₗ[R] ℳ q) q f) =
      (ℳ q).subtype.comp f := by
  rw [gradedOperatorMap, DirectSum.toModule_lof]
  rfl

/-- Each component of an assembled operator is the corresponding homogeneous map. -/
@[simp]
theorem decompose_gradedOperatorMap (f : ⨁ q, H →ₗ[R] ℳ q) (a : H) (q : ι) :
    DirectSum.decompose ℳ (gradedOperatorMap ℳ f a) q = f q a := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i f =>
    rw [← DirectSum.lof_eq_of R, gradedOperatorMap_lof]
    by_cases hi : i = q
    · subst q
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, DirectSum.decompose_coe,
        DirectSum.lof_eq_of, DirectSum.of_eq_same]
    · apply Subtype.ext
      rw [LinearMap.comp_apply]
      simp only [Submodule.subtype_apply, DirectSum.decompose_of_mem_ne ℳ (f a).property hi,
        DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi), LinearMap.zero_apply,
        Submodule.coe_zero]
  | add f g hf hg => simp [hf, hg]

/-- The homogeneous maps can be recovered from their assembled operator. -/
theorem gradedOperatorMap_injective : Function.Injective (gradedOperatorMap (H := H) ℳ) := by
  intro f g hfg
  ext q a
  rw [← decompose_gradedOperatorMap ℳ f a q, ← decompose_gradedOperatorMap ℳ g a q, hfg]

/-- An operator is assembled from finitely many homogeneous maps exactly when
one finite set supports the outputs of every input simultaneously. -/
theorem mem_range_gradedOperatorMap_iff (f : H →ₗ[R] M) :
    f ∈ LinearMap.range (gradedOperatorMap ℳ) ↔
      ∃ S : Finset ι, ∀ q ∉ S, (homogeneousComponent ℳ q).comp f = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.support, fun q hq => ?_⟩
    ext a
    simp only [LinearMap.comp_apply, homogeneousComponent_apply, decompose_gradedOperatorMap]
    rw [DFinsupp.notMem_support_iff.mp hq, LinearMap.zero_apply, Submodule.coe_zero]
    rfl
  · rintro ⟨S, hS⟩
    let g : ⨁ q, H →ₗ[R] ℳ q := DFinsupp.mk S fun q =>
      (DirectSum.component R ι (fun q => ℳ q) q.val).comp
        ((DirectSum.decomposeLinearEquiv ℳ).toLinearMap.comp f)
    refine ⟨g, ?_⟩
    ext a
    apply (DirectSum.decompose ℳ).injective
    ext q
    rw [decompose_gradedOperatorMap]
    simp only [g, DFinsupp.mk_apply]
    split_ifs with hq
    · rfl
    · have hz := DFunLike.congr_fun (hS q hq) a
      simpa only [LinearMap.comp_apply, homogeneousComponent_apply, LinearMap.zero_apply,
        Submodule.coe_zero] using hz.symm

/-- Linear families with a uniform finite homogeneous support. -/
abbrev GradedOperators (H : Type*) [AddCommMonoid H] [Module R H] : Type _ :=
  LinearMap.range (gradedOperatorMap (H := H) ℳ)

namespace GradedOperators

/-- The direct sum of homogeneous operators identifies with its image in all linear maps. -/
def equiv : (⨁ q, H →ₗ[R] ℳ q) ≃ₗ[R] GradedOperators ℳ H :=
  LinearEquiv.ofInjective _ (gradedOperatorMap_injective ℳ)

@[simp]
theorem coe_equiv (f : ⨁ q, H →ₗ[R] ℳ q) :
    (equiv ℳ f : H →ₗ[R] M) = gradedOperatorMap ℳ f :=
  LinearEquiv.ofInjective_apply _ _

/-- Include one whole homogeneous linear family. -/
def single (q : ι) : (H →ₗ[R] ℳ q) →ₗ[R] GradedOperators ℳ H :=
  (equiv ℳ).toLinearMap.comp (DirectSum.lof R ι (fun q => H →ₗ[R] ℳ q) q)

@[simp]
theorem coe_single (q : ι) (f : H →ₗ[R] ℳ q) :
    (single ℳ q f : H →ₗ[R] M) = (ℳ q).subtype.comp f := by
  simp [single]

/-- The degree-`q` operators, with their inherited internal decomposition. -/
def grading (q : ι) : Submodule R (GradedOperators ℳ H) :=
  (DirectSum.summand R (fun q => H →ₗ[R] ℳ q) q).comap (equiv ℳ).symm.toLinearMap

/-- Membership in one degree means that every output lies in that homogeneous piece. -/
@[simp]
theorem mem_grading_iff (q : ι) (f : GradedOperators ℳ H) :
    f ∈ grading ℳ q ↔ ∀ a, f.val a ∈ ℳ q := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := DirectSum.mem_summand.mp hf
    have he := congrArg (fun g => (equiv ℳ g : H →ₗ[R] M)) hg
    rw [← DirectSum.lof_eq_of R, coe_equiv, gradedOperatorMap_lof,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at he
    intro a
    rw [← he]
    exact (g a).property
  · intro hf
    let g : H →ₗ[R] ℳ q := f.val.codRestrict (ℳ q) hf
    have he : equiv ℳ (DirectSum.lof R ι (fun q => H →ₗ[R] ℳ q) q g) = f := by
      apply Subtype.ext
      simp only [coe_equiv, gradedOperatorMap_lof]
      rfl
    rw [grading, Submodule.mem_comap, ← he, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
    exact DirectSum.lof_mem_summand _ _

instance : DirectSum.Decomposition (grading (H := H) ℳ) :=
  TauCeti.DirectSum.Decomposition.restrict
    (DirectSum.summand R (fun q => H →ₗ[R] ℳ q)) (grading ℳ)
    (equiv ℳ).symm.toLinearMap (equiv ℳ).symm.injective
    (fun _ _ => by rw [grading, Submodule.mem_comap]) (fun _ _ => (equiv ℳ).symm.surjective _)

/-- Evaluation at one incoming coefficient. -/
def eval (a : H) : GradedOperators ℳ H →ₗ[R] M :=
  (LinearMap.applyₗ a).comp (LinearMap.range (gradedOperatorMap (H := H) ℳ)).subtype

omit [DirectSum.Decomposition ℳ] in
@[simp]
theorem eval_apply (a : H) (f : GradedOperators ℳ H) : eval ℳ a f = f.val a := (rfl)

/-- A homogeneous family is admitted in its specified operator degree. -/
theorem single_mem (q : ι) (f : H →ₗ[R] ℳ q) : single ℳ q f ∈ grading ℳ q := by
  rw [mem_grading_iff]
  intro a
  rw [coe_single, LinearMap.comp_apply, Submodule.subtype_apply]
  exact (f a).property

/-- A homogeneous operator piece is the full module of maps into that piece.
Uniform finite support places no restriction on a single homogeneous map. -/
def pieceEquiv (q : ι) : grading (H := H) ℳ q ≃ₗ[R] (H →ₗ[R] ℳ q) where
  toFun f := f.val.val.codRestrict (ℳ q) ((mem_grading_iff ℳ q f.val).mp f.property)
  invFun g := ⟨single ℳ q g, single_mem ℳ q g⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    ext a
    simp only [coe_single, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.codRestrict_apply]
  right_inv g := by
    ext a
    simp only [LinearMap.codRestrict_apply, coe_single, LinearMap.comp_apply,
      Submodule.subtype_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pieceEquiv_apply (q : ι) (f : grading (H := H) ℳ q) (a : H) :
    (pieceEquiv ℳ q f a : M) = eval ℳ a f.val := (eval_apply ℳ a f.val).symm

@[simp]
theorem pieceEquiv_symm_apply (q : ι) (f : H →ₗ[R] ℳ q) :
    ((pieceEquiv ℳ q).symm f : GradedOperators ℳ H) = single ℳ q f := (rfl)

/-- Evaluation preserves the homogeneous degree, even if it kills the operator. -/
theorem eval_mem (a : H) {q : ι} {f : GradedOperators ℳ H} (hf : f ∈ grading ℳ q) :
    eval ℳ a f ∈ ℳ q := (mem_grading_iff ℳ q f).mp hf a

/-- Taking a homogeneous component commutes with evaluation. -/
@[simp↓]
theorem eval_decompose (a : H) (f : GradedOperators ℳ H) (q : ι) :
    eval ℳ a (DirectSum.decompose (grading ℳ) f q) =
      (DirectSum.decompose ℳ (eval ℳ a f) q : M) :=
  DirectSum.map_decompose_shift (grading ℳ) ℳ (eval ℳ a).toAddMonoidHom id
    Function.injective_id (fun _ _ hf => eval_mem ℳ a hf) q f

end GradedOperators
end Mei
