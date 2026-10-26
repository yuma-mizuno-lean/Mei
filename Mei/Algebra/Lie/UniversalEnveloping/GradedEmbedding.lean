/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.Degree.Map
public import Mei.Algebra.Lie.Derivation.Embedding
public import Mei.Algebra.Lie.Derivation.Graded
public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration

/-!
# Degree reflection by the canonical enveloping map

When the canonical Lie map into an enveloping algebra is injective, it reflects
the degree filtration. Quotienting by a degree ideal therefore kills precisely
the Lie elements supported above the same cutoff. Over a commutative rational
algebra, a grading with zero weight only on the
zero piece makes the canonical map injective: its Euler derivation gives a
faithful sheared representation. This includes every positive integral grading.
The argument uses `LieDerivation.ShearedModule`, rather than a PBW basis.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  [DecidableEq Γ] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] (d : Γ →+ ℤ)

/-- The preimage of an enveloping degree ideal is the corresponding Lie degree tail,
provided the canonical enveloping map is injective. -/
theorem comap_degreeFiltration_ι (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (hι : Function.Injective (ι R : L → _root_.UniversalEnvelopingAlgebra R L)) (k : ℕ) :
    (((degreeFiltration ℒ d hneg).ideal k).restrictScalars R).comap
        (ι R : L →ₗ⁅R⁆ _root_.UniversalEnvelopingAlgebra R L).toLinearMap =
      Mei.DirectSum.degreeTail ℒ d k := by
  rw [degreeFiltration_ideal, Mei.GradedAlgebra.degreeIdeal_restrictScalars]
  exact LinearMap.comap_degreeTail_eq_of_injective _ ℒ (homogeneousSubmodule ℒ)
    hι (fun _ _ hx => ι_mem_homogeneousSubmodule ℒ hx) d k

/-- Over a commutative rational algebra, an integral grading whose zero-weight
pieces vanish makes the canonical enveloping map injective. Weights may be negative,
and neither finite cutoffs nor freeness of the homogeneous pieces is required. -/
theorem ι_injective_of_nonzero_grading [Algebra ℚ R]
    (hzero : ∀ n, d n = 0 → ℒ n = ⊥) :
    Function.Injective (ι R : L → _root_.UniversalEnvelopingAlgebra R L) := by
  apply (LieDerivation.ofGrading ℒ ((Int.castAddHom R).comp d)).ι_injective_of_injective
  apply LieDerivation.ofGrading_injective
  intro n x y hxy
  by_cases hn : d n = 0
  · apply Subtype.ext
    have hx : (x : L) = 0 := by simpa only [hzero n hn, Submodule.mem_bot] using x.property
    have hy : (y : L) = 0 := by simpa only [hzero n hn, Submodule.mem_bot] using y.property
    exact hx.trans hy.symm
  · have hq : IsUnit (d n : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn)
    have hr : IsUnit (d n : R) := by simpa only [map_intCast] using hq.map (algebraMap ℚ R)
    obtain ⟨u, hu⟩ := hr
    apply MulAction.injective u
    simpa only [Units.smul_def, hu, AddMonoidHom.comp_apply, Int.coe_castAddHom] using hxy

end Mei.UniversalEnvelopingAlgebra
