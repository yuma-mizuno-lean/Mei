/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic

/-!
# The Lie-degree grading of a universal enveloping algebra

The enveloping algebra of a graded Lie algebra is graded by total Lie degree.
The homogeneous pieces are spans of words in homogeneous Lie elements. This
construction works over any commutative ring, without a basis of the Lie algebra.

Homogeneous projection provides degreewise descriptions of maps and descending
degree ideals even when the homogeneous Lie modules are not free. The construction
follows the universal-property realization of `TensorAlgebra.gradedAlgebra`.
For any additive scalar weight, the lifted grading derivation acts diagonally on
homogeneous pieces and their projections, allowing inverse Euler scaling to reconstruct
Lie representatives from Dynkin values when detecting primitive elements.
-/

public section

open scoped DirectSum

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The span of words in homogeneous Lie elements whose total degree is `n`. -/
def homogeneousSubmodule (n : Γ) : Submodule R U :=
  Submodule.span R {a | ∃ l : List (Σ i, ℒ i), (l.map Sigma.fst).sum = n ∧
    (l.map (fun x => ι R (x.2 : L))).prod = a}

/-- The word-span description of an enveloping homogeneous piece. -/
theorem homogeneousSubmodule_def (n : Γ) :
    homogeneousSubmodule ℒ n =
      Submodule.span R {a | ∃ l : List (Σ i, ℒ i), (l.map Sigma.fst).sum = n ∧
        (l.map (fun x => ι R (x.2 : L))).prod = a} := (rfl)

/-- A submodule contains a homogeneous piece exactly when it contains every word of that degree. -/
theorem homogeneousSubmodule_le_iff (n : Γ) (p : Submodule R U) :
    homogeneousSubmodule ℒ n ≤ p ↔
      ∀ l : List (Σ i, ℒ i), (l.map Sigma.fst).sum = n →
        (l.map (fun x => ι R (x.2 : L))).prod ∈ p := by
  rw [homogeneousSubmodule_def, Submodule.span_le]
  constructor
  · intro h l hl
    exact h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- A homogeneous word belongs to the piece given by its total degree. -/
theorem prod_mem_homogeneousSubmodule (l : List (Σ i, ℒ i)) :
    (l.map (fun x => ι R (x.2 : L))).prod ∈
      homogeneousSubmodule ℒ (l.map Sigma.fst).sum :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- Lie generators retain their original degree in the enveloping algebra. -/
theorem ι_mem_homogeneousSubmodule {n : Γ} {x : L} (hx : x ∈ ℒ n) :
    ι R x ∈ homogeneousSubmodule ℒ n := by
  simpa using prod_mem_homogeneousSubmodule ℒ [⟨n, x, hx⟩]

/-- The homogeneous word spans are compatible with the algebra product. -/
instance homogeneousSubmodule_gradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule ℒ) where
  one_mem := Submodule.subset_span ⟨[], by simp, rfl⟩
  mul_mem := by
    intro m n a b ha hb
    have hmul : homogeneousSubmodule ℒ m * homogeneousSubmodule ℒ n ≤
        homogeneousSubmodule ℒ (m + n) := by
      rw [homogeneousSubmodule_def, homogeneousSubmodule_def,
        Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      simpa [hl, ht] using prod_mem_homogeneousSubmodule ℒ (l ++ t)
    exact hmul (Submodule.mul_mem_mul ha hb)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

private noncomputable def gradedιLinear : L →ₗ[R] ⨁ n, homogeneousSubmodule ℒ n :=
  (_root_.DirectSum.lmap fun n =>
    (((ι R : L →ₗ⁅R⁆ U).toLinearMap.comp (ℒ n).subtype).codRestrict _
      fun x => ι_mem_homogeneousSubmodule ℒ x.property)).comp
    (_root_.DirectSum.decomposeLinearEquiv ℒ).toLinearMap

private theorem gradedιLinear_apply {n : Γ} (x : ℒ n) :
    gradedιLinear ℒ x = _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) n
      ⟨ι R (x : L), ι_mem_homogeneousSubmodule ℒ x.property⟩ := by
  simp only [gradedιLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    _root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.decompose_coe,
    _root_.DirectSum.lmap_of]
  rfl

private theorem gradedιLinear_map_lie (x y : L) :
    gradedιLinear ℒ ⁅x, y⁆ = ⁅gradedιLinear ℒ x, gradedιLinear ℒ y⁆ := by
  induction x using _root_.DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | add x z hx hz => simp only [add_lie, map_add, hx, hz]
  | @homogeneous i x =>
    induction y using _root_.DirectSum.Decomposition.inductionOn ℒ with
    | zero => simp
    | add y z hy hz => simp only [lie_add, map_add, hy, hz]
    | @homogeneous j y =>
      have hxy := SetLike.GradedBracket.bracket_mem x.property y.property
      rw [gradedιLinear_apply ℒ ⟨_, hxy⟩, gradedιLinear_apply, gradedιLinear_apply]
      simp only [LieRing.of_associative_ring_bracket, _root_.DirectSum.of_mul_of]
      simp only [vadd_eq_add]
      have hswap :
          _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) (j + i)
              (GradedMonoid.GMul.mul (A := fun n : Γ => ↥(homogeneousSubmodule ℒ n))
                ⟨ι R (y : L), ι_mem_homogeneousSubmodule ℒ y.property⟩
                ⟨ι R (x : L), ι_mem_homogeneousSubmodule ℒ x.property⟩) =
            _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) (i + j)
              ⟨ι R (y : L) * ι R (x : L), by
                simpa only [add_comm j i] using SetLike.mul_mem_graded
                  (ι_mem_homogeneousSubmodule ℒ y.property)
                  (ι_mem_homogeneousSubmodule ℒ x.property)⟩ :=
        by
          apply _root_.DirectSum.of_eq_of_gradedMonoid_eq
          apply Sigma.subtype_ext (add_comm j i)
          rfl
      rw [hswap, ← map_sub]
      congr 1
      apply Subtype.ext
      simpa only [LieRing.of_associative_ring_bracket, Submodule.coe_sub,
        SetLike.coe_gMul, Subtype.coe_mk] using
        LieHom.map_lie (ι R) (x : L) (y : L)

private noncomputable def gradedι : L →ₗ⁅R⁆ ⨁ n, homogeneousSubmodule ℒ n :=
  { gradedιLinear ℒ with map_lie' := fun {x y} => gradedιLinear_map_lie ℒ x y }

private theorem gradedι_apply {n : Γ} (x : ℒ n) :
    gradedι ℒ x = _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) n
      ⟨ι R (x : L), ι_mem_homogeneousSubmodule ℒ x.property⟩ :=
  by
    calc gradedι ℒ x = gradedιLinear ℒ x := rfl
         _ = _ := gradedιLinear_apply ℒ x

/-- Recompose homogeneous Lie generators in their degrees and extend to the enveloping algebra. -/
noncomputable def decomposeAlgHom : U →ₐ[R] ⨁ n, homogeneousSubmodule ℒ n :=
  lift R (gradedι ℒ)

/-- The decomposition homomorphism places a homogeneous Lie generator in its original degree. -/
theorem decomposeAlgHom_ι_apply {n : Γ} (x : ℒ n) :
    decomposeAlgHom ℒ (ι R (x : L)) = _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) n
      ⟨ι R (x : L), ι_mem_homogeneousSubmodule ℒ x.property⟩ := by
  rw [decomposeAlgHom, lift_ι_apply, gradedι_apply]

/-- Recomposition after the grading homomorphism is the identity. -/
@[simp]
theorem coeAlgHom_comp_decomposeAlgHom :
    (_root_.DirectSum.coeAlgHom (homogeneousSubmodule ℒ)).comp (decomposeAlgHom ℒ) =
      AlgHom.id R U := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  ext x
  induction x using _root_.DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | homogeneous x =>
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
      AlgHom.id_apply, decomposeAlgHom_ι_apply, _root_.DirectSum.coeAlgHom_of]

private theorem decomposeAlgHom_prod (l : List (Σ i, ℒ i)) :
    decomposeAlgHom ℒ (l.map (fun x => ι R (x.2 : L))).prod =
      _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) (l.map Sigma.fst).sum
        ⟨(l.map (fun x => ι R (x.2 : L))).prod, prod_mem_homogeneousSubmodule ℒ l⟩ := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, _root_.DirectSum.one_def]; rfl
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, decomposeAlgHom_ι_apply, ih,
      _root_.DirectSum.of_mul_of]
    congr 1

/-- The decomposition homomorphism places each homogeneous element in its prescribed summand. -/
@[simp]
theorem decomposeAlgHom_apply (n : Γ) (x : homogeneousSubmodule ℒ n) :
    decomposeAlgHom ℒ (x : U) =
      _root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) n x := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    subst n
    exact decomposeAlgHom_prod ℒ l
  | zero =>
    rw [map_zero]
    exact (map_zero (_root_.DirectSum.of (fun n => ↥(homogeneousSubmodule ℒ n)) n)).symm
  | add x y hx hy hxi hyi =>
    rw [map_add, hxi, hyi, ← map_add]
    rfl
  | smul r x hx hxi =>
    rw [map_smul, hxi, ← _root_.DirectSum.of_smul]
    rfl

/-- A grading on a Lie algebra induces the total Lie-degree grading of its enveloping algebra,
over an arbitrary commutative ring and without a basis hypothesis. -/
noncomputable instance gradedAlgebra : _root_.GradedAlgebra (homogeneousSubmodule ℒ) := (by
  apply _root_.GradedAlgebra.ofAlgHom _ (decomposeAlgHom ℒ)
  · exact coeAlgHom_comp_decomposeAlgHom ℒ
  · exact decomposeAlgHom_apply ℒ)

/-- The enveloping lift used to construct the grading is its canonical decomposition map. -/
theorem decomposeAlgHom_eq_decomposeAlgEquiv :
    decomposeAlgHom ℒ =
      (_root_.DirectSum.decomposeAlgEquiv (homogeneousSubmodule ℒ)).toAlgHom := by
  apply DFunLike.ext
  intro x
  induction x using _root_.DirectSum.Decomposition.inductionOn (homogeneousSubmodule ℒ) with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | homogeneous x =>
    simp only [decomposeAlgHom_apply, AlgEquiv.coe_toAlgHom,
      _root_.DirectSum.decomposeAlgEquiv_apply, _root_.DirectSum.decompose_coe]

/-- Canonical Lie inclusion preserves homogeneous components. -/
theorem ι_component (x : L) (n : Γ) :
    _root_.UniversalEnvelopingAlgebra.ι R (DirectSum.decompose ℒ x n : L) =
      (DirectSum.decompose (homogeneousSubmodule ℒ)
        (_root_.UniversalEnvelopingAlgebra.ι R x) n : U) :=
  DirectSum.map_decompose_shift ℒ (homogeneousSubmodule ℒ)
    (_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U).toLinearMap.toAddMonoidHom
    (fun i => i) Function.injective_id
    (fun _ _ hx => Mei.UniversalEnvelopingAlgebra.ι_mem_homogeneousSubmodule ℒ hx) n x

section Euler

variable (φ : Γ →+ R)

local notation "𝒰" => homogeneousSubmodule ℒ
local notation "E" => LieDerivation.ofGrading ℒ φ
local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L E

private theorem euler_word (l : List (Σ n, ℒ n)) :
    (Y : Module.End R U) (l.map (fun x => _root_.UniversalEnvelopingAlgebra.ι R (x.2 : L))).prod =
      φ (l.map Sigma.fst).sum •
        (l.map (fun x => _root_.UniversalEnvelopingAlgebra.ι R (x.2 : L))).prod := by
  induction l with
  | nil => simp [TauCeti.derivationLieAlgebra.apply_one_eq_zero]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons,
      TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mul,
      TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι,
      LieDerivation.ofGrading_apply_apply ℒ _ x.2.property, map_smul, ih,
      map_add, add_smul, smul_mul_assoc, mul_smul_comm]

/-- The lifted grading derivation acts by its scalar weight on each homogeneous piece. -/
theorem euler_homogeneous {n : Γ} {a : U} (ha : a ∈ 𝒰 n) :
    (Y : Module.End R U) a = φ n • a := by
  rw [Mei.UniversalEnvelopingAlgebra.homogeneousSubmodule_def] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [hl] using euler_word ℒ φ l
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb, smul_add]
  | smul r a _ ha => simp only [map_smul, ha, smul_comm r]

/-- The lifted grading derivation acts diagonally on homogeneous components. -/
theorem euler_component (a : U) (n : Γ) :
    (DirectSum.decompose 𝒰 ((Y : Module.End R U) a) n : U) =
      φ n • (DirectSum.decompose 𝒰 a n : U) := by
  have hhom (i : Γ) (x : U) (hx : x ∈ 𝒰 i) : (Y : Module.End R U) x ∈ 𝒰 i := by
    rw [euler_homogeneous ℒ φ hx]
    exact (𝒰 i).smul_mem _ hx
  have h := DirectSum.map_decompose_shift 𝒰 𝒰 (Y : Module.End R U).toAddMonoidHom
    (fun i => i) Function.injective_id hhom n a
  simp only [LinearMap.toAddMonoidHom_coe] at h
  rw [euler_homogeneous ℒ φ (DirectSum.decompose 𝒰 a n).property] at h
  exact h.symm

end Euler

section Nat

variable (ℒ : ℕ → Submodule R L) [GradedLieAlgebra ℒ]

/-- The degree-zero component is the scalar counit when the Lie degree-zero piece vanishes. -/
theorem component_zero_eq_counit (hzero : ℒ 0 = ⊥) (a : U) :
    (DirectSum.decompose (homogeneousSubmodule ℒ) a 0 : U) =
      algebraMap R U (Coalgebra.counit (R := R) a) := by
  have h : GradedRing.projZeroRingHom (homogeneousSubmodule ℒ) =
      (algebraMap R U).comp (Bialgebra.counitAlgHom R U).toRingHom := by
    apply RingHom.ext
    intro a
    induction a using TauCeti.UniversalEnvelopingAlgebra.induction_ι R L with
    | ι x =>
      have hx0 : (DirectSum.decompose ℒ x 0 : L) = 0 := by
        simpa only [hzero, Submodule.mem_bot] using
          (DirectSum.decompose ℒ x 0).property
      simp only [GradedRing.projZeroRingHom_apply, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Bialgebra.counitAlgHom_apply,
        TauCeti.UniversalEnvelopingAlgebra.counit_ι, map_zero]
      rw [← ι_component, hx0, map_zero]
    | algebraMap r =>
      rw [GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
          (SetLike.algebraMap_mem_graded (homogeneousSubmodule ℒ) r)]
      simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul a b ha hb => simp only [map_mul, ha, hb]
  exact DFunLike.congr_fun h a

end Nat

end Mei.UniversalEnvelopingAlgebra
