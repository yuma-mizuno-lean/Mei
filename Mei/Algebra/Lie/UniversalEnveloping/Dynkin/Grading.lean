/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Grading
public import Mei.Algebra.Lie.UniversalEnveloping.Dynkin.Basic

/-!
# Euler derivations on graded enveloping algebras

The lifted Euler derivation acts by total degree on homogeneous pieces and their
projections. These formulas let inverse Euler scaling reconstruct Lie representatives
from Dynkin values when detecting primitive elements.
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

end Mei.UniversalEnvelopingAlgebra
