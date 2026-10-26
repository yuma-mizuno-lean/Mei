/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Sign.Completion

/-!
# Completed sign factors under regrading

A graded Lie homomorphism over a positive degree map carries sign subgroups for
a pulled-back character into the target sign subgroups. At finite order its source
cutoff is controlled by the degree map's modulus. On completions it commutes with
extraction of all three sign factors, even when degrees merge or homogeneous
pieces are killed. In particular, extracting a completed middle factor commutes
with a degree-preserving coefficient map.

This gives the sign-factor comparison for coefficient maps and changes of degree
without choosing compatible finite factorizations anew. It uses the homogeneous
component criterion `Mei.mem_signSubalgebra_iff`,
`Mei.GradedLieHom.truncatedMap_mem`, and uniqueness in
`Mei.PositiveDegrees.completedSignFactorizationEquiv`. For the underlying sign
factorization and its attribution to Bridgeland, see
`Mei.Algebra.Lie.BCH.Sign.Basic`.
-/

public section

noncomputable section

universe u

namespace Mei.GradedLieHom

open PositiveDegrees

variable {N M R A : Type*} {L L' : Type u}
  [AddCommMonoid N] [AddCommMonoid M] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [DecidableEq M]
  [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  {d : PositiveDegrees N} {e : PositiveDegrees M}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ]
  {T : PositiveDegreeMap d e} (f : GradedLieHom T ℒ ℳ) (φ : M →+ A)

/-- A finite graded map preserves sign subgroups for the pulled-back character,
using any source cutoff at least as large as its prescribed modulus. -/
theorem truncatedMap_mem_signSubgroup {a k : ℕ} (h : T.modulus k ≤ a)
    {s : SignType} {g : d.truncatedGroup ℒ a}
    (hg : g ∈ (signSubalgebra (d.truncatedGrading ℒ a)
      (φ.comp T.toAddMonoidHom) s).bchSubgroup) :
    (f.truncatedMap k h).bchGroupMap g ∈
      (signSubalgebra (e.truncatedGrading ℳ k) φ s).bchSubgroup := by
  classical
  rw [LieSubalgebra.mem_bchSubgroup] at hg ⊢
  rw [LieHom.log_bchGroupMap]
  have hc := (mem_signSubalgebra_iff (d.truncatedGrading ℒ a)
    (φ.comp T.toAddMonoidHom)).mp hg
  rw [← DirectSum.sum_support_decompose (d.truncatedGrading ℒ a) (BCHGroup.log g), map_sum]
  rw [← LieSubalgebra.mem_toSubmodule]
  apply Submodule.sum_mem
  intro n _
  by_cases hn : SignType.sign (φ (T n)) = s
  · have hy := f.truncatedMap_mem k h
      (DirectSum.decompose (d.truncatedGrading ℒ a) (BCHGroup.log g) n).property
    simpa only [hn] using le_signSubalgebra (e.truncatedGrading ℳ k) φ (T n) hy
  · rw [hc n (by simpa only [AddMonoidHom.comp_apply] using hn), map_zero]
    exact Submodule.zero_mem _

/-- The completed map takes each pulled-back sign subgroup into the corresponding
target sign subgroup, with no injectivity assumption on the degree map. -/
theorem completedMap_mem_signSubgroup {s : SignType} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ completedSignSubgroup ℒ (φ.comp T.toAddMonoidHom) d s) :
    f.completedMap g ∈ completedSignSubgroup ℳ φ e s := by
  rw [mem_completedSignSubgroup] at hg ⊢
  intro k
  rw [projection_completedMap]
  exact f.truncatedMap_mem_signSubgroup φ le_rfl (hg (T.modulus k))

/-- Regrading commutes with extraction of completed positive, zero and negative
factors, when the source character is the pullback of the target character. -/
@[simp]
theorem completedMap_completedSignFactorizationEquiv_symm
    (g : d.completedBCHGroup ℒ) (s : SignType) :
    f.completedMap
        ((completedSignFactorizationEquiv ℒ (φ.comp T.toAddMonoidHom) d).symm g s :
          d.completedBCHGroup ℒ) =
      ((completedSignFactorizationEquiv ℳ φ e).symm (f.completedMap g) s :
        e.completedBCHGroup ℳ) := by
  let a := (completedSignFactorizationEquiv ℒ (φ.comp T.toAddMonoidHom) d).symm g
  let b : ∀ t, completedSignSubgroup ℳ φ e t :=
    fun t => ⟨f.completedMap (a t), f.completedMap_mem_signSubgroup φ (a t).property⟩
  have hb : completedSignFactorizationEquiv ℳ φ e b = f.completedMap g := by
    simpa only [completedSignFactorizationEquiv_apply, b, map_mul] using
      congrArg f.completedMap
        ((completedSignFactorizationEquiv ℒ (φ.comp T.toAddMonoidHom) d).apply_symm_apply g)
  exact congrArg (fun c => (c s : e.completedBCHGroup ℳ))
    ((completedSignFactorizationEquiv ℳ φ e).eq_symm_apply.mpr hb)

end Mei.GradedLieHom
