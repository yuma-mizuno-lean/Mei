/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Global PBW symmetrization and its filtered surjectivity

For a Lie algebra over a commutative rational algebra, `pbwSymmetrization` is
the linear map from the symmetric algebra to the enveloping algebra obtained
by averaging products over permutations. Every element of PBW filtration degree
at most `k` has a symmetric preimage of degree at most `k`. In particular the map
is surjective, without freeness or flatness assumptions on the Lie algebra.

This assembles Tau Ceti's `pbwHomogeneousSymmetrization` using the homogeneous
decomposition of the symmetric algebra. Its leading-symbol identity and
`pbwHomogeneousComponentMap_surjective` supply the filtered lifting argument.
The scalar ring lies in `Type`, as required by the degreewise symmetric-power
construction; the Lie algebra has an independent universe.

The symmetrization construction is classical; see Dixmier, *Enveloping
Algebras*, §2.4. For its role over rational algebras without a freeness
hypothesis, see Petracci, *Universal representations of Lie algebras by
coderivations*, §8 (arXiv:math/0303020v1).
-/

public noncomputable section

namespace Mei.UniversalEnvelopingAlgebra

open TauCeti.UniversalEnvelopingAlgebra TauCeti.SymmetricAlgebra
open scoped TensorProduct

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)
local notation "𝒮" => homogeneousSubmodule R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- The canonical linear symmetrization map, averaging each homogeneous
symmetric tensor over all orders of its Lie generators. -/
def pbwSymmetrization : SymmetricAlgebra R L →ₗ[R] U :=
  (DirectSum.toModule R ℕ U (fun n => pbwHomogeneousSymmetrization R L n
    (IsUnit.natCast_factorial_of_algebra ℚ n))).comp
      (DirectSum.decomposeLinearEquiv 𝒮).toLinearMap

/-- On a homogeneous symmetric polynomial the global map is the existing
degreewise symmetrization. The degree is supplied by the membership hypothesis. -/
theorem pbwSymmetrization_of_mem {n : ℕ} {p : SymmetricAlgebra R L} (hp : p ∈ 𝒮 n) :
    pbwSymmetrization R L p = pbwHomogeneousSymmetrization R L n
      (IsUnit.natCast_factorial_of_algebra ℚ n) ⟨p, hp⟩ := by
  simp only [pbwSymmetrization, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝒮 hp,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

/-- Multiplying a symmetric tensor and then applying the global map gives the
degreewise permutation average. -/
@[simp]
theorem pbwSymmetrization_toSymmetricAlgebra (n : ℕ) (x : Sym[R]^n L) :
    pbwSymmetrization R L (TauCeti.SymmetricPower.toSymmetricAlgebra R L n x) =
      TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization R L n
        (IsUnit.natCast_factorial_of_algebra ℚ n) x := by
  rw [← TauCeti.SymmetricPower.coe_equivHomogeneous_apply,
    pbwSymmetrization_of_mem R L (TauCeti.SymmetricPower.equivHomogeneous n x).property,
    pbwHomogeneousSymmetrization_equivHomogeneous]

/-- Symmetrization sends a product of generators to the average of their
ordered products, with the usual rational factorial denominator. -/
theorem pbwSymmetrization_prod_ι (n : ℕ) (x : Fin n → L) :
    pbwSymmetrization R L (∏ i, SymmetricAlgebra.ι R L (x i)) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i => ι (x (σ i))).prod := by
  have hp : ∏ i, SymmetricAlgebra.ι R L (x i) ∈ 𝒮 n := by
    simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn, List.length_ofFn] using
      prod_map_ι_mem_homogeneousSubmodule R L (List.ofFn x)
  rw [pbwSymmetrization_of_mem R L hp, pbwHomogeneousSymmetrization_apply,
    TauCeti.SymmetricPower.equivHomogeneous_symm_prod_ι]
  exact TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_tprod_rat R L n _ x

/-- Pure powers are unchanged by averaging their identical factors. -/
@[simp]
theorem pbwSymmetrization_ι_pow (x : L) (n : ℕ) :
    pbwSymmetrization R L (SymmetricAlgebra.ι R L x ^ n) = ι x ^ n := by
  have hp : SymmetricAlgebra.ι R L x ^ n ∈ 𝒮 n := by
    simpa using prod_map_ι_mem_homogeneousSubmodule R L (List.replicate n x)
  rw [pbwSymmetrization_of_mem R L hp, pbwHomogeneousSymmetrization_apply]
  have he : (TauCeti.SymmetricPower.equivHomogeneous (R := R) (M := L) n).symm
      ⟨SymmetricAlgebra.ι R L x ^ n, hp⟩ = ⨂ₛ[R] _ : Fin n, x := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      TauCeti.SymmetricPower.equivHomogeneous_symm_prod_ι (R := R) (M := L)
        n (fun _ => x) (by simpa using hp)
  rw [he]
  exact TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_tprod_const R L n _ x

/-- The global map preserves the unit. -/
@[simp]
theorem pbwSymmetrization_one : pbwSymmetrization R L 1 = 1 := by
  simpa using pbwSymmetrization_ι_pow R L (0 : L) 0

/-- The global map extends the canonical Lie map on generators. -/
@[simp]
theorem pbwSymmetrization_ι (x : L) :
    pbwSymmetrization R L (SymmetricAlgebra.ι R L x) = ι x := by
  simpa using pbwSymmetrization_ι_pow R L x 1

/-- Symmetrization fixes scalars. -/
@[simp]
theorem pbwSymmetrization_algebraMap (r : R) :
    pbwSymmetrization R L (algebraMap R (SymmetricAlgebra R L) r) = algebraMap R U r := by
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, pbwSymmetrization_one]

/-- Symmetrization does not increase word degree. -/
theorem pbwSymmetrization_mem_pbwFiltration {k : ℕ} {p : SymmetricAlgebra R L}
    (hp : p ∈ F k) : pbwSymmetrization R L p ∈ pbwFiltration R L k := by
  have hle : F k ≤ (pbwFiltration R L k).comap (pbwSymmetrization R L) := by
    rw [TauCeti.Algebra.wordFiltration_eq_iSup_pow]
    refine iSup_le fun n => ?_
    intro p hp
    rw [Submodule.mem_comap, pbwSymmetrization_of_mem R L hp]
    exact pbwFiltration_mono R L n.property
      (pbwHomogeneousSymmetrization_mem_pbwFiltration R L n _ _)
  exact hle hp

/-- Every leading PBW symbol can be lifted by a homogeneous symmetric element.
The error has strictly smaller word degree. -/
theorem exists_sub_pbwSymmetrization_mem_previous {k : ℕ} {a : U}
    (ha : a ∈ pbwFiltration R L k) :
    ∃ p : 𝒮 k, a - pbwSymmetrization R L p ∈ pbwFiltrationPrevious R L k := by
  obtain ⟨p, hp⟩ := pbwHomogeneousComponentMap_surjective R L k
    (Submodule.Quotient.mk (⟨a, by simpa only [pbwFiltration_def] using ha⟩ :
      TauCeti.Algebra.wordFiltration (ι).toLinearMap k))
  refine ⟨p, ?_⟩
  rw [← mk_pbwHomogeneousSymmetrization R L k
    (IsUnit.natCast_factorial_of_algebra ℚ k)] at hp
  have hsub := (Submodule.Quotient.eq _).mp hp.symm
  rw [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff] at hsub
  simpa only [Submodule.coe_sub, pbwSymmetrization_of_mem R L p.property,
    pbwFiltrationPrevious_def] using hsub

/-- Every element in PBW filtration degree `k` has a symmetric preimage of
word degree at most `k`, without a freeness assumption. -/
theorem exists_pbwSymmetrization_eq_of_mem {k : ℕ} {a : U}
    (ha : a ∈ pbwFiltration R L k) :
    ∃ p ∈ F k, pbwSymmetrization R L p = a := by
  induction k generalizing a with
  | zero =>
    obtain ⟨p, hp⟩ := exists_sub_pbwSymmetrization_mem_previous R L ha
    have he : a = pbwSymmetrization R L p := by
      simpa only [pbwFiltrationPrevious_zero, Submodule.mem_bot, sub_eq_zero] using hp
    exact ⟨p, TauCeti.Algebra.range_pow_le_wordFiltration _ 0 p.property, he.symm⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := exists_sub_pbwSymmetrization_mem_previous R L ha
    rw [pbwFiltrationPrevious_succ] at hp
    obtain ⟨q, hq, he⟩ := ih hp
    refine ⟨q + p, (F (k + 1)).add_mem
      (TauCeti.Algebra.wordFiltration_mono _ (Nat.le_succ k) hq)
      (TauCeti.Algebra.range_pow_le_wordFiltration _ (k + 1) p.property), ?_⟩
    rw [map_add, he, sub_add_cancel]

/-- Symmetrization maps each symmetric word-filtration step onto precisely
the corresponding PBW step. -/
@[simp]
theorem map_wordFiltration_pbwSymmetrization (k : ℕ) :
    (F k).map (pbwSymmetrization R L) = pbwFiltration R L k := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact pbwSymmetrization_mem_pbwFiltration R L hp
  · intro a ha
    obtain ⟨p, hp, he⟩ := exists_pbwSymmetrization_eq_of_mem R L ha
    exact ⟨p, hp, he⟩

/-- Global symmetrization is surjective over every commutative rational algebra. -/
theorem pbwSymmetrization_surjective : Function.Surjective (pbwSymmetrization R L) := by
  intro a
  obtain ⟨k, hk⟩ := exists_mem_pbwFiltration R L a
  obtain ⟨p, _, hp⟩ := exists_pbwSymmetrization_eq_of_mem R L hk
  exact ⟨p, hp⟩

end Mei.UniversalEnvelopingAlgebra
