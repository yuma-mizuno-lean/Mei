/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Symmetrization.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mei.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# PBW symmetrization preserves the coalgebra structure

The canonical symmetrization from the symmetric algebra to the enveloping
algebra preserves comultiplication and counit over every commutative rational
algebra, without a freeness hypothesis. `pbwSymmetrizationCoalgHom` bundles
these identities for use with coalgebra maps and primitive elements.

The proof uses the existing global `pbwSymmetrization` and its pure-power
formula. Polarization reduces both identities to powers of one generator;
their coproducts agree by Tau Ceti's `Bialgebra.comul_pow_of_primitive`.
See Dixmier, *Enveloping Algebras*, §2.4, and Petracci, *Universal
representations of Lie algebras by coderivations*, §8 (arXiv:math/0303020v1).
-/

public noncomputable section

namespace Mei.UniversalEnvelopingAlgebra

open scoped TensorProduct

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

local notation "S" => SymmetricAlgebra R L
local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- PBW symmetrization intertwines the symmetric and enveloping coproducts,
without freeness or flatness assumptions on the Lie algebra. -/
theorem comul_pbwSymmetrization (p : S) :
    Coalgebra.comul (R := R) (pbwSymmetrization R L p) =
      TensorProduct.map (pbwSymmetrization R L) (pbwSymmetrization R L)
        (Coalgebra.comul p) := by
  have he : (Coalgebra.comul (R := R) : U →ₗ[R] U ⊗[R] U).comp
      (pbwSymmetrization R L) =
      (TensorProduct.map (pbwSymmetrization R L) (pbwSymmetrization R L)).comp
        (Coalgebra.comul (R := R) : S →ₗ[R] S ⊗[R] S) := by
    apply LinearMap.ext_on_range (Mei.SymmetricAlgebra.span_range_ι_pow_eq_top R L)
    rintro ⟨x, n⟩
    simp only [LinearMap.comp_apply, pbwSymmetrization_ι_pow]
    rw [TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow,
      TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R L x)]
    simp only [map_sum, map_nsmul, TensorProduct.map_tmul, pbwSymmetrization_ι_pow]
  exact LinearMap.congr_fun he p

/-- PBW symmetrization preserves the counit. -/
@[simp]
theorem counit_pbwSymmetrization (p : S) :
    Coalgebra.counit (R := R) (pbwSymmetrization R L p) = Coalgebra.counit p := by
  have he : (Coalgebra.counit (R := R) : U →ₗ[R] R).comp
      (pbwSymmetrization R L) = (Coalgebra.counit (R := R) : S →ₗ[R] R) := by
    apply LinearMap.ext_on_range (Mei.SymmetricAlgebra.span_range_ι_pow_eq_top R L)
    rintro ⟨x, n⟩
    simp
  exact LinearMap.congr_fun he p

/-- Canonical PBW symmetrization as a coalgebra homomorphism. Its underlying
linear map is the permutation-averaging map `pbwSymmetrization`. -/
def pbwSymmetrizationCoalgHom : S →ₗc[R] U where
  __ := pbwSymmetrization R L
  counit_comp := LinearMap.ext (counit_pbwSymmetrization R L)
  map_comp_comul := LinearMap.ext fun p => (comul_pbwSymmetrization R L p).symm

/-- The bundled coalgebra map has exactly the original underlying linear map. -/
@[simp]
theorem coe_pbwSymmetrizationCoalgHom :
    (pbwSymmetrizationCoalgHom R L : S →ₗ[R] U) = pbwSymmetrization R L :=
  (rfl)

/-- Evaluation of the bundled map is the original symmetrization. -/
@[simp]
theorem pbwSymmetrizationCoalgHom_apply (p : S) :
    pbwSymmetrizationCoalgHom R L p = pbwSymmetrization R L p :=
  (rfl)

end Mei.UniversalEnvelopingAlgebra
