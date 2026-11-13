/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.RestrictScalars
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom
public import TauCeti.Algebra.Lie.Quotient

/-!
# Restriction of scalars for graded Lie algebras

A grading of a Lie algebra remains a grading after restricting scalars in its
homogeneous pieces. Its homogeneous components have the same underlying values.
This supplies the graded Lie algebra structure over a smaller coefficient ring
without freeness or flatness assumptions.

For a positive grading, the degree ideals restrict on the same carriers. Consequently
finite Lie truncation commutes with restriction of scalars, preserving homogeneous
pieces, homogeneous projections and transitions between cutoffs. The comparison uses
Mathlib's `Submodule.quotEquivOfEq` and Mei's `LieIdeal.quotientRestrictScalarsEquiv`.
Graded homomorphisms restrict with the same degree map and cutoff modulus, and
their finite quotient maps commute with these comparisons.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

variable {R S L ι : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [DecidableEq ι] [AddCommMonoid ι] (ℒ : ι → Submodule S L)

namespace TauCeti.GradedLieHom

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  {L' : Type*} [LieRing L'] [LieAlgebra S L'] [LieAlgebra R L']
  [IsScalarTower R S L'] {d : PositiveDegrees N} {e : PositiveDegrees M}
  {T : PositiveDegreeMap d e} {ℋ : N → Submodule S L} {ℳ : M → Submodule S L'}

/-- Restrict a graded Lie homomorphism without changing its degree map or cutoff modulus. -/
def restrictScalars (f : GradedLieHom T ℋ ℳ) (R : Type*) [CommRing R]
    [LieAlgebra R L] [LieAlgebra R L'] [SMul R S]
    [IsScalarTower R S L] [IsScalarTower R S L'] :
    GradedLieHom T (fun n => (ℋ n).restrictScalars R)
      (fun m => (ℳ m).restrictScalars R) where
  toLieHom := f.toLieHom.restrictScalars R
  map_mem hx := by simpa using f.map_mem hx

/-- Scalar restriction preserves the values of a graded Lie homomorphism. -/
@[simp]
theorem restrictScalars_apply (f : GradedLieHom T ℋ ℳ) (x : L) :
    f.restrictScalars R x = f x := by
  simp only [← coe_toLieHom, restrictScalars, LieHom.restrictScalars_apply]

/-- The underlying Lie map is the scalar restriction of the original map. -/
@[simp]
theorem toLieHom_restrictScalars (f : GradedLieHom T ℋ ℳ) :
    (f.restrictScalars R).toLieHom = f.toLieHom.restrictScalars R := (rfl)

/-- Restricting scalars preserves the identity graded homomorphism. -/
@[simp]
theorem restrictScalars_id :
    (id (d := d) ℋ).restrictScalars R = id (fun n => (ℋ n).restrictScalars R) := by
  ext x
  simp

/-- Restricting scalars preserves composition and its composite cutoff modulus. -/
@[simp]
theorem restrictScalars_comp {P : Type*} [AddCommMonoid P]
    {L'' : Type*} [LieRing L''] [LieAlgebra S L''] [LieAlgebra R L'']
    [IsScalarTower R S L''] {p : PositiveDegrees P} {U : PositiveDegreeMap e p}
    {ℐ : P → Submodule S L''} (g : GradedLieHom U ℳ ℐ) (f : GradedLieHom T ℋ ℳ) :
    (g.comp f).restrictScalars R = (g.restrictScalars R).comp (f.restrictScalars R) := by
  ext x
  simp

end TauCeti.GradedLieHom

namespace TauCeti.GradedLieHom

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  [DecidableEq N] [DecidableEq M]
  {L' : Type*} [LieRing L'] [LieAlgebra S L'] [LieAlgebra R L']
  [IsScalarTower R S L'] {d : PositiveDegrees N} {e : PositiveDegrees M}
  {T : PositiveDegreeMap d e} {ℋ : N → Submodule S L} {ℳ : M → Submodule S L'}
  [GradedLieAlgebra ℋ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℋ] [IsPositiveGrading e ℳ]

/-- The finite quotient maps commute with restriction of scalars, including regraded maps
whose source cutoff is prescribed by a modulus. -/
theorem truncatedMap_restrictScalars (f : GradedLieHom T ℋ ℳ) {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) :
    (e.truncatedRestrictScalarsEquiv (R := R) ℳ k).toLieHom.comp
        ((f.restrictScalars R).truncatedMap k h) =
      ((f.truncatedMap k h).restrictScalars R).comp
        (d.truncatedRestrictScalarsEquiv (R := R) ℋ a).toLieHom := by
  apply (d.degreeIdeal (fun n => (ℋ n).restrictScalars R) a).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end TauCeti.GradedLieHom
