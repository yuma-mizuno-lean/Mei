/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Completion

/-!
# Naturality of BCH sign factors

Degree-preserving Lie homomorphisms commute with the positive, middle and negative
factors of finite and completed BCH elements. In particular, extracting a middle
factor and then changing Lie coefficients gives the same wall label as extracting
the middle factor after changing coefficients. No injectivity or surjectivity is
required, so factors that become identities under specialization are included.

The proofs use the uniqueness in `PositiveDegrees.signFactorizationEquiv` and
its completed projection formula, together with `map_mem_signSubalgebra`.
For the sign factorization of Bridgeland that these maps respect, see
`Mei.Algebra.Lie.BCH.Sign.Basic`.
-/

public section

noncomputable section

namespace Mei.GradedLieHom

universe u

variable {N R A : Type*} {L L' : Type u} [AddCommMonoid N] [DecidableEq N]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  {d : PositiveDegrees N} {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]

open PositiveDegrees

/-- A degree-preserving map carries every finite sign factor to the corresponding
factor of its image, even when the target cutoff is smaller. -/
theorem truncatedMap_signFactorizationEquiv_symm
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (θ : N →+ A)
    {k l : ℕ} (hkl : (PositiveDegreeMap.id d).modulus k ≤ l)
    (g : d.truncatedGroup ℒ l) (s : SignType) :
    (f.truncatedMap (a := l) k hkl).bchGroupMap
        ((signFactorizationEquiv ℒ θ d l).symm g s : d.truncatedGroup ℒ l) =
      ((signFactorizationEquiv ℳ θ d k).symm
        ((f.truncatedMap (a := l) k hkl).bchGroupMap g) s : d.truncatedGroup ℳ k) := by
  let F := (f.truncatedMap (a := l) k hkl).bchGroupMap
  let a := (signFactorizationEquiv ℒ θ d l).symm g
  let b : ∀ s, (signSubalgebra (d.truncatedGrading ℳ k) θ s).bchSubgroup := fun s =>
    ⟨F (a s), by
      rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
      exact map_mem_signSubalgebra (d.truncatedGrading ℒ l) θ
        (d.truncatedGrading ℳ k) (f.truncatedMap (a := l) k hkl).toLinearMap.toAddMonoidHom
        (fun _ _ hx => by simpa only [LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
          PositiveDegreeMap.id_apply] using f.truncatedMap_mem k hkl hx)
        ((LieSubalgebra.mem_bchSubgroup _ _).mp (a s).property)⟩
  have hb : signFactorizationEquiv ℳ θ d k b = F g := by
    rw [signFactorizationEquiv_apply]
    simp only [b, ← map_mul]
    have ha := (signFactorizationEquiv ℒ θ d l).apply_symm_apply g
    rw [signFactorizationEquiv_apply] at ha
    exact congrArg F ha
  exact congrArg (fun a => (a s : d.truncatedGroup ℳ k))
    ((signFactorizationEquiv ℳ θ d k).eq_symm_apply.mpr hb)

/-- Completed coefficient change commutes with extracting every sign factor,
including the middle factor used to label a wall. -/
theorem completedMap_completedSignFactorizationEquiv_symm
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (θ : N →+ A)
    (g : d.completedBCHGroup ℒ) (s : SignType) :
    f.completedMap
        ((completedSignFactorizationEquiv ℒ θ d).symm g s : d.completedBCHGroup ℒ) =
      ((completedSignFactorizationEquiv ℳ θ d).symm (f.completedMap g) s :
        d.completedBCHGroup ℳ) := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_completedMap, projection_completedSignFactorizationEquiv_symm]
  exact f.truncatedMap_signFactorizationEquiv_symm θ le_rfl _ s

end Mei.GradedLieHom
