/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Basic

/-!
# Naturality of finite sign factors

A degree-preserving Lie homomorphism carries each factor of a truncated BCH
element to the corresponding factor of its image. In particular, extracting
the middle factor commutes with coefficient changes, even when the homomorphism
kills homogeneous pieces. This is the algebraic naturality needed for wall labels
defined by sign factorization.

The proof uses `map_mem_signSubalgebra`, `LieHom.bchGroupMap`, and uniqueness
in `PositiveDegrees.signFactorizationEquiv`. For the source of the sign
factorization itself, see `Mei.Algebra.Lie.BCH.Sign.Basic`.
-/

public section

noncomputable section

namespace Mei.GradedLieHom

variable {N R L L' A : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  {d : PositiveDegrees N} {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]

/-- Degree-preserving Lie maps commute with extraction of every finite sign factor. -/
@[simp]
theorem truncatedMap_signFactorizationEquiv_symm
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (θ : N →+ A)
    (k : ℕ) (g : d.truncatedGroup ℒ k) (s : SignType) :
    (f.truncatedMap k (by simp)).bchGroupMap
        ((PositiveDegrees.signFactorizationEquiv ℒ θ d k).symm g s :
          d.truncatedGroup ℒ k) =
      ((PositiveDegrees.signFactorizationEquiv ℳ θ d k).symm
        ((f.truncatedMap k (by simp)).bchGroupMap g) s : d.truncatedGroup ℳ k) := by
  let F : d.truncatedGroup ℒ k →* d.truncatedGroup ℳ k :=
    (f.truncatedMap k (by simp)).bchGroupMap
  let a := (PositiveDegrees.signFactorizationEquiv ℒ θ d k).symm g
  have hf (n) (x) (hx : x ∈ d.truncatedGrading ℒ k n) :
      f.truncatedMap k (by simp) x ∈ d.truncatedGrading ℳ k n := by
    simpa only [PositiveDegreeMap.id_apply] using f.truncatedMap_mem k (by simp) hx
  let b : ∀ t, (signSubalgebra (d.truncatedGrading ℳ k) θ t).bchSubgroup :=
    fun t => ⟨F (a t), by
      rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
      exact map_mem_signSubalgebra (d.truncatedGrading ℒ k) θ
        (d.truncatedGrading ℳ k) (f.truncatedMap k (by simp)).toLinearMap.toAddMonoidHom
        hf ((LieSubalgebra.mem_bchSubgroup _ _).mp (a t).property)⟩
  have hb : PositiveDegrees.signFactorizationEquiv ℳ θ d k b = F g := by
    rw [PositiveDegrees.signFactorizationEquiv_apply]
    simpa only [b, ← map_mul, PositiveDegrees.signFactorizationEquiv_apply] using
      congrArg F ((PositiveDegrees.signFactorizationEquiv ℒ θ d k).apply_symm_apply g)
  exact congrArg (fun c => (c s : d.truncatedGroup ℳ k))
    ((PositiveDegrees.signFactorizationEquiv ℳ θ d k).eq_symm_apply.mpr hb)

end Mei.GradedLieHom
