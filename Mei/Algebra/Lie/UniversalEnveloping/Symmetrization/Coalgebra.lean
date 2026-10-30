/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Symmetrization
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
import Mei.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# PBW symmetrization as a coalgebra map

The global PBW symmetrization map preserves coproduct and counit over every
commutative rational algebra, without a freeness hypothesis on the Lie algebra.
We bundle it as a coalgebra homomorphism. Combined with its filtered
surjectivity, this supplies the coalgebra comparison needed to identify
primitive elements via symmetric tensors.

The proof uses pure-power spanning in the symmetric algebra,
`pbwSymmetrization_ι_pow`, and Tau Ceti's binomial coproduct formula for powers
of primitive elements. The classical symmetrization construction and its
coalgebra compatibility are described in Dixmier, *Enveloping Algebras*, §2.4;
see also Petracci, *Universal representations of Lie algebras by coderivations*,
§8 (arXiv:math/0303020v1), for the setting of arbitrary rational algebras.
-/

public noncomputable section

namespace Mei.UniversalEnvelopingAlgebra

open scoped TensorProduct

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "S" => SymmetricAlgebra R L
local notation "sym" => pbwSymmetrization R L

/-- PBW symmetrization preserves the counit, over arbitrary commutative rational
algebras and arbitrary Lie algebras. -/
@[simp]
theorem counit_pbwSymmetrization (p : S) :
    Coalgebra.counit (R := R) (sym p) = Coalgebra.counit (R := R) p := by
  have he : (Coalgebra.counit (R := R) (A := U)).comp sym =
      Coalgebra.counit (R := R) (A := S) := by
    apply Mei.SymmetricAlgebra.linearMap_ext_ι_pow R L
    intro x n
    simp only [LinearMap.comp_apply, pbwSymmetrization_ι_pow, Bialgebra.counit_pow,
      TauCeti.UniversalEnvelopingAlgebra.counit_ι, SymmetricAlgebra.counit_ι]
  exact LinearMap.congr_fun he p

/-- PBW symmetrization intertwines the standard primitive-generator coproducts.
This requires neither freeness nor flatness of the Lie algebra. -/
@[simp]
theorem comul_pbwSymmetrization (p : S) :
    Coalgebra.comul (R := R) (sym p) =
      TensorProduct.map sym sym (Coalgebra.comul (R := R) p) := by
  have he : (Coalgebra.comul (R := R) (A := U)).comp sym =
      (TensorProduct.map sym sym).comp (Coalgebra.comul (R := R) (A := S)) := by
    apply Mei.SymmetricAlgebra.linearMap_ext_ι_pow R L
    intro x n
    simp only [LinearMap.comp_apply, pbwSymmetrization_ι_pow,
      TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow,
      TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R L x),
      map_sum, map_nsmul, TensorProduct.map_tmul]
  exact LinearMap.congr_fun he p

/-- The canonical symmetrization coalgebra homomorphism. Its underlying linear
map is the permutation average `pbwSymmetrization`. -/
def pbwSymmetrizationCoalgHom : S →ₗc[R] U where
  toLinearMap := sym
  counit_comp := LinearMap.ext (counit_pbwSymmetrization R L)
  map_comp_comul := LinearMap.ext fun p => (comul_pbwSymmetrization R L p).symm

/-- The coalgebra homomorphism has exactly the original symmetrization map
as its underlying linear map. -/
@[simp]
theorem coe_pbwSymmetrizationCoalgHom :
    (pbwSymmetrizationCoalgHom R L : S →ₗ[R] U) = sym := (rfl)

/-- Evaluate the bundled map using the original symmetrization API. -/
@[simp]
theorem pbwSymmetrizationCoalgHom_apply (p : S) :
    pbwSymmetrizationCoalgHom R L p = sym p := (rfl)

end Mei.UniversalEnvelopingAlgebra
