/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.RestrictScalars
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom
public import Mei.Algebra.Lie.Quotient.Map
public import Mei.Algebra.Lie.RestrictScalars
public import Mei.Algebra.PositiveDegrees.RestrictScalars

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

variable {R S L ι : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [DecidableEq ι] [AddCommMonoid ι] (ℒ : ι → Submodule S L)

/-- Restricting scalars preserves a bracket-compatible internal grading. -/
instance GradedLieAlgebra.restrictScalars [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (fun i => (ℒ i).restrictScalars R) where
  toDecomposition := inferInstance
  bracket_mem := SetLike.GradedBracket.bracket_mem (ℒ := ℒ) (ℳ := ℒ)

namespace Mei.GradedLieHom

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

end Mei.GradedLieHom

namespace Mei.PositiveDegrees

variable (d : Mei.PositiveDegrees ι) [GradedLieAlgebra ℒ] [Mei.IsPositiveGrading d ℒ]

/-- The degree ideal of the restricted grading is the restriction of the degree ideal. -/
@[simp]
theorem degreeIdeal_restrictScalars (k : ℕ) :
    d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k =
      (d.degreeIdeal ℒ k).restrictScalars R := by
  apply LieSubmodule.toSubmodule_injective
  simp

/-- Restricting scalars commutes with finite Lie truncation. -/
def truncatedRestrictScalarsEquiv (k : ℕ) :
    d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      d.truncatedLie ℒ k := by
  let e : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ[R]
      L ⧸ (d.degreeIdeal ℒ k).restrictScalars R :=
    Submodule.quotEquivOfEq (R := R)
      (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).toSubmodule
      ((d.degreeIdeal ℒ k).restrictScalars R).toSubmodule (by simp)
  have he (x : L) : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
    Submodule.quotEquivOfEq_mk _ _ _ x
  let e' : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k ≃ₗ⁅R⁆
      L ⧸ (d.degreeIdeal ℒ k).restrictScalars R :=
    { e with
      map_lie' {x y} := by
        induction x using Submodule.Quotient.induction_on with | _ x
        induction y using Submodule.Quotient.induction_on with | _ y
        -- Expose the linear equivalence behind the Lie-equivalence structure fields.
        change e (Submodule.Quotient.mk ⁅x, y⁆) =
          ⁅e (Submodule.Quotient.mk x), e (Submodule.Quotient.mk y)⁆
        rw [he, he, he]
        exact LieSubmodule.Quotient.mk_bracket _ _ _ }
  exact e'.trans ((d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R)

/-- The truncation comparison preserves representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_mk (k : ℕ) (x : L) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp only [truncatedRestrictScalarsEquiv, LieEquiv.trans_apply]
  -- The first Lie equivalence wraps a linear equivalence; expose it to use its API.
  change (d.degreeIdeal ℒ k).quotientRestrictScalarsEquiv R
      (Submodule.quotEquivOfEq (R := R)
        (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).toSubmodule
        ((d.degreeIdeal ℒ k).restrictScalars R).toSubmodule (by simp)
        (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
  rw [Submodule.quotEquivOfEq_mk, LieIdeal.quotientRestrictScalarsEquiv_mk]

/-- The inverse comparison preserves quotient representatives. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_symm_mk (k : ℕ) (x : L) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  apply (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).injective
  simp

/-- The comparison intertwines the restricted quotient projection and the quotient projection
of the restricted grading. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_comp_mkQ (k : ℕ) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) k).mkQ =
      (d.degreeIdeal ℒ k).mkQ.restrictScalars R := by
  ext x
  simp [LieIdeal.mkQ_apply]

/-- The comparison identifies homogeneous pieces with their restrictions of scalars. -/
theorem map_truncatedGrading_restrictScalars (k : ℕ) (n : ι) :
    (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n).map
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearMap =
      (d.truncatedGrading ℒ k n).restrictScalars R := by
  simp only [truncatedGrading_eq, ← Submodule.map_comp, Submodule.restrictScalars_map]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact d.truncatedRestrictScalarsEquiv_mk (R := R) ℒ k x

/-- The comparison identifies the homogeneous pieces in the two truncations. -/
theorem truncatedRestrictScalarsEquiv_mem_iff (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k x ∈ d.truncatedGrading ℒ k n ↔
      x ∈ d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n := by
  rw [← Submodule.restrictScalars_mem R, ← d.map_truncatedGrading_restrictScalars ℒ k n]
  have he : (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearEquiv.toLinearMap =
      (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearMap := by
    ext y
    simp
  have h := Submodule.mem_map_equiv
      (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k n)
      (e := (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearEquiv)
      (x := (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLinearEquiv x)
  simp only [LinearEquiv.symm_apply_apply] at h
  simpa only [he, LieEquiv.coe_toLinearEquiv] using h

/-- Homogeneous projection commutes with the scalar-restriction comparison. -/
@[simp]
theorem truncatedRestrictScalarsEquiv_decompose (k : ℕ) (n : ι)
    (x : d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) :
    d.truncatedRestrictScalarsEquiv (R := R) ℒ k
        (DirectSum.decompose (d.truncatedGrading (fun n => (ℒ n).restrictScalars R) k) x n :
          d.truncatedLie (fun n => (ℒ n).restrictScalars R) k) =
      (DirectSum.decompose (d.truncatedGrading ℒ k)
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ k x) n : d.truncatedLie ℒ k) := by
  induction x using Submodule.Quotient.induction_on with | _ x
  simp

/-- The finite-order comparisons commute with transitions to smaller cutoffs. -/
theorem truncatedRestrictScalarsEquiv_naturality {k l : ℕ} (h : k ≤ l) :
    (d.truncatedRestrictScalarsEquiv (R := R) ℒ k).toLieHom.comp
        ((d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).factor _
          (d.degreeIdeal_antitone _ h)) =
      (((d.degreeIdeal ℒ l).factor _ (d.degreeIdeal_antitone ℒ h)).restrictScalars R).comp
        (d.truncatedRestrictScalarsEquiv (R := R) ℒ l).toLieHom := by
  apply (d.degreeIdeal (fun n => (ℒ n).restrictScalars R) l).lieHom_qext
  intro x
  simp [LieIdeal.mkQ_apply]

end Mei.PositiveDegrees

namespace Mei.GradedLieHom

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

end Mei.GradedLieHom
