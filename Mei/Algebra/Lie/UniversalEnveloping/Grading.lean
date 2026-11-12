/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Grading
public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation.Basic

/-!
# Euler derivations on graded enveloping algebras

A grading derivation of the Lie algebra lifts to the enveloping algebra, where
it acts diagonally with the same weights on the homogeneous pieces.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra
open TauCeti.UniversalEnvelopingAlgebra (homogeneousSubmodule homogeneousSubmodule_def)

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie inclusion commutes with extracting a homogeneous component. -/
theorem ι_component (x : L) (n : Γ) :
    ι R (DirectSum.decompose ℒ x n : L) =
      (DirectSum.decompose (homogeneousSubmodule ℒ) (ι R x) n : U) := by
  simp only [ι_apply, TauCeti.UniversalEnvelopingAlgebra.coe_decompose_mkAlgHom_ι]

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
  rw [TauCeti.UniversalEnvelopingAlgebra.homogeneousSubmodule_def] at ha
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

end Mei.UniversalEnvelopingAlgebra
