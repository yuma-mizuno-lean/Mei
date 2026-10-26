/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Basic

/-!
# Naturality of sign factorization

A degree-preserving Lie homomorphism carries each finite sign factor to the
corresponding factor of its image. In particular, middle-factor wall labels
commute with changes of coefficients, even for noninjective maps.

This uses `Mei.map_mem_signSubalgebra`, `LieHom.bchGroupMap`, and uniqueness
of `Mei.PositiveDegrees.signFactorizationEquiv`; no choice of factorization
is added to the interface.
-/

public section

namespace Mei.GradedLieHom

variable {N R L L' A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  {d : PositiveDegrees N} {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]

/-- Every finite sign factor is natural under a degree-preserving Lie map. -/
@[simp]
theorem truncatedMap_signFactorizationEquiv_symm
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (θ : N →+ A) (k : ℕ)
    (g : d.truncatedGroup ℒ k) (s : SignType) :
    (f.truncatedMap (a := k) k (by simp)).bchGroupMap
        ((PositiveDegrees.signFactorizationEquiv ℒ θ d k).symm g s :
          d.truncatedGroup ℒ k) =
      ((PositiveDegrees.signFactorizationEquiv ℳ θ d k).symm
        ((f.truncatedMap (a := k) k (by simp)).bchGroupMap g) s : d.truncatedGroup ℳ k) := by
  let a := (PositiveDegrees.signFactorizationEquiv ℒ θ d k).symm g
  let b : ∀ t, (signSubalgebra (d.truncatedGrading ℳ k) θ t).bchSubgroup := fun t =>
    ⟨(f.truncatedMap (a := k) k (by simp)).bchGroupMap (a t), by
      rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
      exact map_mem_signSubalgebra (d.truncatedGrading ℒ k) θ
        (d.truncatedGrading ℳ k) (f.truncatedMap (a := k) k (by simp)).toLinearMap.toAddMonoidHom
        (fun _ _ hx => by
        simpa only [PositiveDegreeMap.id_apply, LinearMap.toAddMonoidHom_coe,
          LieHom.coe_toLinearMap] using
          f.truncatedMap_mem (a := k) k (by simp) hx)
        ((LieSubalgebra.mem_bchSubgroup _ _).mp (a t).property)⟩
  have hb : PositiveDegrees.signFactorizationEquiv ℳ θ d k b =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap g := by
    simpa only [PositiveDegrees.signFactorizationEquiv_apply, b, map_mul] using
      congrArg (f.truncatedMap (a := k) k (by simp)).bchGroupMap
        ((PositiveDegrees.signFactorizationEquiv ℒ θ d k).apply_symm_apply g)
  exact congrArg (fun c => (c s : d.truncatedGroup ℳ k))
    ((PositiveDegrees.signFactorizationEquiv ℳ θ d k).eq_symm_apply.mpr hb)

end Mei.GradedLieHom
