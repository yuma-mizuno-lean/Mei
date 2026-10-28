/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Abelian
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mathlib.Algebra.Lie.SemiDirect

/-!
# The graded Lie algebra of a module probe

A positively graded Lie algebra acts on every shifted coefficient module. Giving
that module zero internal bracket makes its semidirect sum with the acting Lie
algebra the module probe: the original Lie algebra has charge zero and the
coefficients have charge one. Their ambient degree and the charge determine the
extended degree in `ModuleProbe.positiveDegrees`.

The construction uses Mathlib's `LieAlgebra.SemiDirectSum` and the existing
restricted action `PositiveDegrees.shiftedLieSubmodule`. This is the algebraic
module probe of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.ModuleProbe

variable {R M Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)

/-- Shifted coefficients, regarded as an abelian Lie algebra for the module probe. -/
abbrev ModuleCoefficients : Type _ := AbelianLie (shiftedSubmodule ℳ d.monoid p)

/-- The coefficient summand has zero internal bracket. -/
@[simp]
theorem moduleCoefficients_lie (a b : ModuleCoefficients d ℳ p) : ⁅a, b⁆ = 0 :=
  AbelianLie.lie_eq_zero a b

/-- Forget the zero bracket on the shifted coefficient summand. -/
def moduleCoefficientsEquiv : ModuleCoefficients d ℳ p ≃ₗ[R] shiftedSubmodule ℳ d.monoid p :=
  AbelianLie.linearEquiv R

variable [DecidableEq Γ] {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Transport the restricted representation through the coefficient equivalence. -/
private def actionEndHom : L →ₗ⁅R⁆ Module.End R (ModuleCoefficients d ℳ p) :=
  (moduleCoefficientsEquiv d ℳ p).symm.lieConj.toLieHom.comp
    (LieModule.toEnd R L (d.shiftedLieSubmodule ℒ ℳ p))

/-- The original Lie action acts by derivations on the abelian coefficient summand. -/
def actionDerivationHom :
    L →ₗ⁅R⁆ LieDerivation R (ModuleCoefficients d ℳ p) (ModuleCoefficients d ℳ p) where
  toFun x :=
    { toLinearMap := actionEndHom d ℳ p ℒ x
      leibniz' a b := by
        simp only [moduleCoefficients_lie, sub_zero]
        exact map_zero _ }
  map_add' x y := by
    ext a
    exact LinearMap.congr_fun (map_add (actionEndHom d ℳ p ℒ) x y) a
  map_smul' r x := by
    ext a
    exact LinearMap.congr_fun (map_smul (actionEndHom d ℳ p ℒ) r x) a
  map_lie' {x y} := by
    ext a
    exact LinearMap.congr_fun (LieHom.map_lie (actionEndHom d ℳ p ℒ) x y) a

/-- Forgetting the abelian internal bracket recovers the restricted Lie action. -/
@[simp]
theorem moduleCoefficientsEquiv_actionDerivationHom (x : L) (a : ModuleCoefficients d ℳ p) :
    moduleCoefficientsEquiv d ℳ p (actionDerivationHom d ℳ p (ℒ := ℒ) x a) =
      -- The carrier of the restricted Lie submodule is the shifted submodule;
      -- this annotation selects its restricted action rather than the zero bracket.
      ⁅x, (show d.shiftedLieSubmodule ℒ ℳ p from moduleCoefficientsEquiv d ℳ p a)⁆ := by
  simp [actionDerivationHom, actionEndHom, LinearEquiv.conj_apply_apply,
    LieModule.toEnd]

/-- The semidirect Lie algebra of the module probe. Its coefficient summand is
Mathlib's left factor and its original Lie algebra is the right factor. -/
abbrev ProbeLie :=
  LieAlgebra.SemiDirectSum (ModuleCoefficients d ℳ p) L (actionDerivationHom d ℳ p (ℒ := ℒ))

section RationalScalars

variable [Algebra ℚ R]

/-- Rational scalars on the probe are induced by its coefficient ring. -/
scoped instance rationalLieAlgebra : LieAlgebra ℚ (ProbeLie d ℳ p ℒ) where
  toModule := Module.compHom _ (algebraMap ℚ R)
  lie_smul r x y := lie_smul (algebraMap ℚ R r) x y

end RationalScalars

/-- Include the original Lie algebra in charge zero. -/
abbrev baseInclusion : L →ₗ⁅R⁆ ProbeLie d ℳ p ℒ :=
  LieAlgebra.SemiDirectSum.inr (actionDerivationHom d ℳ p (ℒ := ℒ))

/-- Include shifted coefficients as the abelian charge-one ideal. -/
abbrev moduleInclusion : ModuleCoefficients d ℳ p →ₗ⁅R⁆ ProbeLie d ℳ p ℒ :=
  LieAlgebra.SemiDirectSum.inl (actionDerivationHom d ℳ p (ℒ := ℒ))

/-- The bracket of two coefficient inputs vanishes in the probe. -/
theorem lie_moduleInclusion (a b : ModuleCoefficients d ℳ p) :
    ⁅moduleInclusion d ℳ p ℒ a, moduleInclusion d ℳ p ℒ b⁆ = 0 := by
  rw [← LieHom.map_lie, moduleCoefficients_lie, map_zero]

/-- The mixed bracket is exactly the original restricted coefficient action. -/
theorem lie_baseInclusion_moduleInclusion (x : L) (a : ModuleCoefficients d ℳ p) :
    ⁅baseInclusion d ℳ p ℒ x, moduleInclusion d ℳ p ℒ a⁆ =
      moduleInclusion d ℳ p ℒ (actionDerivationHom d ℳ p (ℒ := ℒ) x a) := by
  apply LieAlgebra.SemiDirectSum.ext <;> simp [baseInclusion, moduleInclusion]

/-- Homogeneous base elements shift coefficient homogeneity by their degree. -/
theorem actionDerivationHom_mem_shiftedGrading {n q : Γ} {x : L}
    {a : ModuleCoefficients d ℳ p} (hx : x ∈ ℒ n)
    (ha : moduleCoefficientsEquiv d ℳ p a ∈ shiftedGrading ℳ d.monoid p q) :
    moduleCoefficientsEquiv d ℳ p (actionDerivationHom d ℳ p (ℒ := ℒ) x a) ∈
      shiftedGrading ℳ d.monoid p (n + q) := by
  rw [moduleCoefficientsEquiv_actionDerivationHom, mem_shiftedGrading,
    LieSubmodule.coe_bracket]
  simpa only [vadd_eq_add, add_left_comm] using
    SetLike.GradedBracket.bracket_mem hx ((mem_shiftedGrading ℳ d.monoid p).mp ha)

end Mei.ModuleProbe
