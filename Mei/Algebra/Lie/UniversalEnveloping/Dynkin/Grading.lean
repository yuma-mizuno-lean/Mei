/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Grading
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Euler derivations on graded enveloping algebras

The lifted Euler derivation acts by total degree. Homogeneous projection commutes
with the canonical Lie inclusion; a vanishing Lie degree-zero piece identifies
the enveloping degree-zero projection with its scalar counit.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ℕ → Submodule R L) [GradedLieAlgebra ℒ]
attribute [local instance 100] LieRing.ofAssociativeRing
local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ
local notation "E" => LieDerivation.ofGrading ℒ (Nat.castAddMonoidHom R)
local notation "Y" => TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation R L E
private theorem euler_word (l : List (Σ n, ℒ n)) :
    (Y : Module.End R U) (l.map (fun x => _root_.UniversalEnvelopingAlgebra.ι R (x.2 : L))).prod =
      ((l.map Sigma.fst).sum : R) •
        (l.map (fun x => _root_.UniversalEnvelopingAlgebra.ι R (x.2 : L))).prod := by
  induction l with
  | nil => simp [TauCeti.derivationLieAlgebra.apply_one_eq_zero]
  | cons x l ih =>
    have hcast : (Nat.castAddMonoidHom R) x.1 = (x.1 : R) := rfl
    simp only [List.map_cons, List.prod_cons, List.sum_cons,
      TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_mul,
      TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι,
      LieDerivation.ofGrading_apply_apply ℒ _ x.2.property, map_smul, ih,
      Nat.cast_add, hcast, add_smul, smul_mul_assoc, mul_smul_comm]

/-- The enveloping Euler derivation acts by degree on each homogeneous piece. -/
theorem euler_homogeneous {n : ℕ} {a : U} (ha : a ∈ 𝒰 n) :
    (Y : Module.End R U) a = (n : R) • a := by
  rw [Mei.UniversalEnvelopingAlgebra.homogeneousSubmodule_def] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    simpa only [hl] using euler_word ℒ l
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb, smul_add]
  | smul r a _ ha => simp only [map_smul, ha, smul_comm r]

/-- Canonical Lie inclusion preserves homogeneous components. -/
theorem ι_component (x : L) (n : ℕ) :
    _root_.UniversalEnvelopingAlgebra.ι R (DirectSum.decompose ℒ x n : L) =
      (DirectSum.decompose 𝒰 (_root_.UniversalEnvelopingAlgebra.ι R x) n : U) :=
  DirectSum.map_decompose_shift ℒ 𝒰
    (_root_.UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U).toLinearMap.toAddMonoidHom
    (fun i => i) Function.injective_id
    (fun _ _ hx => Mei.UniversalEnvelopingAlgebra.ι_mem_homogeneousSubmodule ℒ hx) n x

/-- The enveloping Euler derivation acts diagonally on homogeneous components. -/
theorem euler_component (a : U) (n : ℕ) :
    (DirectSum.decompose 𝒰 ((Y : Module.End R U) a) n : U) =
      (n : R) • (DirectSum.decompose 𝒰 a n : U) := by
  have hhom (i : ℕ) (x : U) (hx : x ∈ 𝒰 i) : (Y : Module.End R U) x ∈ 𝒰 i := by
    rw [euler_homogeneous ℒ hx]
    exact (𝒰 i).smul_mem _ hx
  have h := DirectSum.map_decompose_shift 𝒰 𝒰 (Y : Module.End R U).toAddMonoidHom
    (fun i => i) Function.injective_id hhom n a
  simp only [LinearMap.toAddMonoidHom_coe] at h
  rw [euler_homogeneous ℒ (DirectSum.decompose 𝒰 a n).property] at h
  exact h.symm

/-- The degree-zero component is the scalar counit when the Lie degree-zero piece vanishes. -/
theorem component_zero_eq_counit (hzero : ℒ 0 = ⊥) (a : U) :
    (DirectSum.decompose 𝒰 a 0 : U) = algebraMap R U (Coalgebra.counit (R := R) a) := by
  have h : GradedRing.projZeroRingHom 𝒰 =
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
        DirectSum.decompose_of_mem_same 𝒰 (SetLike.algebraMap_mem_graded 𝒰 r)]
      simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul a b ha hb => simp only [map_mul, ha, hb]
  exact DFunLike.congr_fun h a


end Mei.UniversalEnvelopingAlgebra
