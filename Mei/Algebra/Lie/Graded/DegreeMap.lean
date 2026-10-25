/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.PositiveDegreeHom

/-!
# Graded Lie maps and degree truncation towers

The graded Lie homomorphisms from
`Mei.Algebra.Lie.Graded.PositiveDegreeHom` induce maps between truncation towers.
These maps commute with the surjective transitions and remain compatible when
the source cutoff is increased. In particular, they provide compatible
finite-order maps for inverse-limit constructions.

The quotient constructions use `LieIdeal.mapQ` and `LieIdeal.factor`, retaining
the original quotient carriers and computing on representatives.
-/

public section

namespace Mei

variable {N N' R L L' : Type*}
  [AddCommMonoid N] [AddCommMonoid N'] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

namespace GradedLieHom

variable {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [DecidableEq N] [DecidableEq N'] [GradedLieAlgebra ℒ] [GradedLieAlgebra ℒ']
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ']

/-- Increasing the source cutoff changes the induced map only by precomposition
with the source truncation transition. -/
@[simp]
theorem truncatedMap_comp_truncationMap (f : GradedLieHom T ℒ ℒ')
    {k l m : ℕ} (hl : T.modulus k ≤ l) (h : l ≤ m) :
    (f.truncatedMap k hl).comp (d.truncationMap ℒ h) =
      f.truncatedMap k (hl.trans h) := by
  apply (d.degreeIdeal ℒ m).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

/-- The maps of degree truncations commute with the transitions in both towers. -/
theorem truncationMap_comp_truncatedMap (f : GradedLieHom T ℒ ℒ')
    {k l : ℕ} (h : k ≤ l) :
    (e.truncationMap ℒ' h).comp (f.truncatedMap l le_rfl) =
      (f.truncatedMap k le_rfl).comp (d.truncationMap ℒ (T.monotone_modulus h)) := by
  apply (d.degreeIdeal ℒ (T.modulus l)).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end GradedLieHom
end Mei
