/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Map
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.Map

/-!
# Naturality of shifted coefficient actions

A homogeneous coefficient map equivariant along a graded Lie homomorphism
extends to shifted coefficient completions and remains equivariant for their
completed BCH actions. The coefficient shift follows the positive degree map,
and its cutoff modulus permits different truncation orders.

No injectivity or faithfulness of the maps or actions is assumed. This uses the
existing filtered-action naturality theorem on the restricted shifted modules,
in the coefficient setting of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegreeMap

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
  (p : Γ) (φ : GradedLieHom T ℒ ℒ') (f : M →ₗ[R] M')
  (hf : ∀ q, ℳ q ≤ (𝓝 (T q)).comap f)
  (hequiv : ∀ (x : L) (a : M), f ⁅x, a⁆ = ⁅φ x, f a⁆)

include hequiv

/-- Homogeneous equivariant coefficient maps intertwine finite shifted BCH
actions at the source cutoff prescribed by the positive degree map. -/
theorem shiftedQuotientMap_truncatedBCHAction
    (k : ℕ) (g : d.truncatedGroup ℒ (T.modulus k))
    (a : (d.shiftedLieFiltration ℒ ℳ p).quotient (T.modulus k)) :
    T.shiftedQuotientMap ℳ 𝓝 p f hf k
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ (T.modulus k) g a) =
      (e.shiftedLieFiltration ℒ' 𝓝 (T p)).truncatedBCHAction e ℒ' k
        ((φ.truncatedMap k le_rfl).bchGroupMap g)
        (T.shiftedQuotientMap ℳ 𝓝 p f hf k a) := by
  have hcoe (z : d.shiftedLieSubmodule ℒ ℳ p) :
      (T.shiftedMap ℳ 𝓝 p f hf z : M') = f z := T.coe_shiftedMap ℳ 𝓝 p f hf z
  rw [shiftedQuotientMap_def]
  apply (d.shiftedLieFiltration ℒ ℳ p).mapQ_truncatedBCHAction_of_gradedLieHom
    (e.shiftedLieFiltration ℒ' 𝓝 (T p)) φ
  intro x z
  apply Subtype.ext
  simp only [hcoe, LieSubmodule.coe_bracket, hequiv]

/-- Shifted coefficient maps intertwine completed BCH actions along the existing
completed map of the graded Lie homomorphism, on arbitrary completed inputs. -/
theorem shiftedCompletionMap_completedBCHAction
    (g : d.completedBCHGroup ℒ) (a : d.ShiftedCoefficients ℳ p) :
    T.shiftedCompletionMap ℳ 𝓝 p f hf
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g a) =
      (e.shiftedLieFiltration ℒ' 𝓝 (T p)).completedBCHAction e ℒ' (φ.completedMap g)
        (T.shiftedCompletionMap ℳ 𝓝 p f hf a) := by
  let ψ : d.shiftedLieSubmodule ℒ ℳ p →ₗ[R] e.shiftedLieSubmodule ℒ' 𝓝 (T p) :=
    T.shiftedMap ℳ 𝓝 p f hf
  have hψ_coe (z : d.shiftedLieSubmodule ℒ ℳ p) : (ψ z : M') = f z :=
    T.coe_shiftedMap ℳ 𝓝 p f hf z
  have hrestricted (x : L) (z : d.shiftedLieSubmodule ℒ ℳ p) :
      ψ ⁅x, z⁆ = ⁅φ x, ψ z⁆ := by
    apply Subtype.ext
    simp only [hψ_coe, LieSubmodule.coe_bracket, hequiv]
  rw [shiftedCompletionMap_def]
  exact (d.shiftedLieFiltration ℒ ℳ p).completionMap_completedBCHAction_of_gradedLieHom
    (e.shiftedLieFiltration ℒ' 𝓝 (T p)) φ ψ
    T.modulus T.monotone_modulus
    (fun k _ hx => T.shiftedMap_mem_shiftedFiltration ℳ 𝓝 p f hf k hx) hrestricted g a

end Mei.PositiveDegreeMap
