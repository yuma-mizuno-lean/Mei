/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.Algebra.Lie.Graded.Shifted.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.DegreeMap

/-!
# Degree-changing naturality of global completed BCH actions

Equivariant homogeneous coefficient maps intertwine global completed actions
along the completed map of a graded Lie homomorphism. Degree fibers may merge;
no injectivity of the degree or coefficient maps is required.

The shifted coefficient setting is motivated by Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 and Definition 2.10
([arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5)).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)
noncomputable section

namespace TauCeti.PositiveDegreeMap

open Mei

variable {Γ Γ' R M M' : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} (T : PositiveDegreeMap d e)
  {ℒ : Γ → Submodule R L} {ℒ' : Γ' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (ℳ : Γ → Submodule R M) (𝓝 : Γ' → Submodule R M')
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝]
  [SetLike.GradedBracket ℒ ℳ] [SetLike.GradedBracket ℒ' 𝓝]
  (φ : GradedLieHom T ℒ ℒ') (f : M →ₗ[R] M')
  (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅φ x, f a⁆)

include hequiv

/-- Coordinate changes of degrees, Lie labels, and module coefficients commute
with the global completed BCH action. The Lie map is supplied explicitly because
a coefficient map need not determine it. -/
theorem shiftedDirectLimitBCHAction_naturality
    (g : d.completedBCHGroup ℒ) (x : d.ShiftedDirectLimit ℳ) :
    T.shiftedDirectLimitMap ℳ 𝓝 f hf (d.shiftedDirectLimitBCHAction ℒ ℳ g x) =
      e.shiftedDirectLimitBCHAction ℒ' 𝓝 (φ.completedMap g)
        (T.shiftedDirectLimitMap ℳ 𝓝 f hf x) := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
  let t := d.coefficientImageChart e T.toAddMonoidHom T.map_mem s
  have ht := d.coefficientImageChart_mem e T.toAddMonoidHom T.map_mem s
  rw [d.shiftedDirectLimitBCHAction_toShiftedDirectLimit,
    T.shiftedDirectLimitMap_toShiftedDirectLimit ℳ 𝓝 f hf s t ht,
    T.shiftedDirectLimitMap_toShiftedDirectLimit ℳ 𝓝 f hf s t ht,
    e.shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart]
  exact congrArg (e.toShiftedDirectLimitOfChart 𝓝 (T (d.coefficientOrigin s)) t ht)
    (T.shiftedCompletionMap_completedBCHAction ℳ 𝓝 (d.coefficientOrigin s) φ f hf hequiv g a)

end TauCeti.PositiveDegreeMap
