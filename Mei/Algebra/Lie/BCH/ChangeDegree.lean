/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion

/-!
# Independence of the positive degree function

Two positive degree functions on the same allowed monoid define canonically
isomorphic completed BCH groups. The comparison is induced by the identity Lie
homomorphism, using the finite-maximum cutoff modulus of
`Mei.PositiveDegreeMap.changeDegree` in each direction.

The equivalence preserves exponentials of original Lie elements and convergent
ordered products, and is natural for graded Lie homomorphisms, even when their
cutoff moduli differ. Reflexivity, symmetry and transitivity make successive
changes of degree coherent.

The construction uses `Mei.GradedLieHom.completedMap`, its composition law and
its independence from the degree map and modulus. In particular, the two cutoff
moduli need not be mutually inverse functions.
-/

public section

noncomputable section

universe u

namespace Mei

namespace PositiveDegrees

variable {N R : Type*} {L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d e p : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ]
  [IsPositiveGrading p ℒ]

private theorem changeDegree_completedMap_self (hP : d.monoid = e.monoid) :
    (GradedLieHom.changeDegree e d hP.symm ℒ).completedMap.comp
      (GradedLieHom.changeDegree d e hP ℒ).completedMap =
        MonoidHom.id (d.completedBCHGroup ℒ) := by
  rw [← GradedLieHom.completedMap_comp]
  exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
    (by simp)).trans GradedLieHom.completedMap_id

/-- Changing a positive degree function on a fixed allowed monoid gives a canonical
isomorphism of completed BCH groups. Its inverse uses the reverse cutoff comparison. -/
def changeDegreeEquiv (hP : d.monoid = e.monoid) :
    d.completedBCHGroup ℒ ≃* e.completedBCHGroup ℒ :=
  (GradedLieHom.changeDegree d e hP ℒ).completedMap.toMulEquiv
    (GradedLieHom.changeDegree e d hP.symm ℒ).completedMap
    (changeDegree_completedMap_self d e ℒ hP)
    (changeDegree_completedMap_self e d ℒ hP.symm)

/-- The forward comparison is the completed map of the identity Lie homomorphism. -/
theorem changeDegreeEquiv_apply (hP : d.monoid = e.monoid) (x : d.completedBCHGroup ℒ) :
    d.changeDegreeEquiv e ℒ hP x = (GradedLieHom.changeDegree d e hP ℒ).completedMap x :=
  (rfl)

/-- Reversing the change of degree gives the inverse comparison. -/
@[simp]
theorem changeDegreeEquiv_symm (hP : d.monoid = e.monoid) :
    (d.changeDegreeEquiv e ℒ hP).symm = e.changeDegreeEquiv d ℒ hP.symm := by
  apply MulEquiv.ext
  intro x
  rfl

/-- Projection computes the comparison at the canonical finite-maximum source cutoff. -/
@[simp]
theorem projection_changeDegreeEquiv (hP : d.monoid = e.monoid) (k : ℕ)
    (x : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (d.changeDegreeEquiv e ℒ hP x) =
      ((GradedLieHom.changeDegree d e hP ℒ).truncatedMap k le_rfl).bchGroupMap
        (CompletedGroup.projection ((PositiveDegreeMap.changeDegree d e hP).modulus k) x) :=
  GradedLieHom.projection_completedMap _ k x

/-- Changing to the same degree function is the identity. -/
@[simp]
theorem changeDegreeEquiv_refl :
    d.changeDegreeEquiv d ℒ rfl = MulEquiv.refl (d.completedBCHGroup ℒ) := by
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun
    ((GradedLieHom.completedMap_eq_of_toLieHom_eq
      (GradedLieHom.changeDegree d d rfl ℒ) (GradedLieHom.id ℒ)
      (by simp)).trans GradedLieHom.completedMap_id) x

/-- Successive changes of degree agree with the direct change. -/
@[simp]
theorem changeDegreeEquiv_trans (hde : d.monoid = e.monoid) (hep : e.monoid = p.monoid) :
    (d.changeDegreeEquiv e ℒ hde).trans (e.changeDegreeEquiv p ℒ hep) =
      d.changeDegreeEquiv p ℒ (hde.trans hep) := by
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun
    ((GradedLieHom.completedMap_comp (GradedLieHom.changeDegree e p hep ℒ)
      (GradedLieHom.changeDegree d e hde ℒ)).symm.trans
        (GradedLieHom.completedMap_eq_of_toLieHom_eq _
          (GradedLieHom.changeDegree d p (hde.trans hep) ℒ) (by simp))) x

/-- The comparison commutes with the canonical exponential map from the Lie algebra. -/
@[simp]
theorem changeDegreeEquiv_expToCompletion (hP : d.monoid = e.monoid) (x : L) :
    d.changeDegreeEquiv e ℒ hP (d.expToCompletion ℒ x) = e.expToCompletion ℒ x := by
  rw [changeDegreeEquiv_apply, GradedLieHom.completedMap_expToCompletion]
  simp

/-- The canonical cutoff modulus controls the change in the completed filtrations.
Applying this also in reverse proves that the two filtrations are cofinal. -/
theorem changeDegreeEquiv_mem_degreeFiltration (hP : d.monoid = e.monoid) (k : ℕ)
    {x : d.completedBCHGroup ℒ}
    (hx : x ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ)
      ((PositiveDegreeMap.changeDegree d e hP).modulus k + 1)) :
    d.changeDegreeEquiv e ℒ hP x ∈
      CompletedGroup.degreeFiltration (e.groupTower ℒ) (k + 1) :=
  (GradedLieHom.changeDegree d e hP ℒ).completedMap_mem_degreeFiltration k hx

variable {ι : Type*}

/-- Finite support at each order is independent of the positive degree function. -/
@[simp]
theorem hasFiniteSupport_changeDegreeEquiv_iff (hP : d.monoid = e.monoid)
    (x : ι → d.completedBCHGroup ℒ) :
    CompletedGroup.HasFiniteSupport (fun i => d.changeDegreeEquiv e ℒ hP (x i)) ↔
      CompletedGroup.HasFiniteSupport x := by
  constructor
  · intro hx
    have h : CompletedGroup.HasFiniteSupport
        (fun i => e.changeDegreeEquiv d ℒ hP.symm (d.changeDegreeEquiv e ℒ hP (x i))) := by
      simpa only [changeDegreeEquiv_apply] using
        (GradedLieHom.changeDegree e d hP.symm ℒ).hasFiniteSupport_completedMap hx
    simpa only [(d.changeDegreeEquiv_symm e ℒ hP).symm, MulEquiv.symm_apply_apply] using h
  · intro hx
    simpa only [changeDegreeEquiv_apply] using
      (GradedLieHom.changeDegree d e hP ℒ).hasFiniteSupport_completedMap hx

/-- The canonical comparison preserves convergent products with the smallest index leftmost. -/
@[simp]
theorem changeDegreeEquiv_orderedProd [LinearOrder ι] (hP : d.monoid = e.monoid)
    (x : ι → d.completedBCHGroup ℒ) (hx : CompletedGroup.HasFiniteSupport x) :
    d.changeDegreeEquiv e ℒ hP (CompletedGroup.orderedProd x hx) =
      CompletedGroup.orderedProd (fun i => d.changeDegreeEquiv e ℒ hP (x i))
        ((d.hasFiniteSupport_changeDegreeEquiv_iff e ℒ hP x).mpr hx) :=
  GradedLieHom.completedMap_orderedProd _ x hx

end PositiveDegrees

namespace GradedLieHom

variable {N M R : Type*} {L L' : Type u}
  [AddCommMonoid N] [AddCommMonoid M] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [DecidableEq M]
  {d e : PositiveDegrees N} {d' e' : PositiveDegrees M}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ]
  [IsPositiveGrading d' ℳ] [IsPositiveGrading e' ℳ]
  {T : PositiveDegreeMap d d'} {U : PositiveDegreeMap e e'}

/-- Changes of degree commute with graded completed maps. Only the underlying Lie
homomorphisms must agree; the degree maps and their moduli may differ. -/
theorem changeDegreeEquiv_naturality (hP : d.monoid = e.monoid)
    (hP' : d'.monoid = e'.monoid) (f : GradedLieHom T ℒ ℳ) (g : GradedLieHom U ℒ ℳ)
    (hfg : f.toLieHom = g.toLieHom) (x : d.completedBCHGroup ℒ) :
    d'.changeDegreeEquiv e' ℳ hP' (f.completedMap x) =
      g.completedMap (d.changeDegreeEquiv e ℒ hP x) := by
  have h := completedMap_eq_of_toLieHom_eq
    ((changeDegree d' e' hP' ℳ).comp f) (g.comp (changeDegree d e hP ℒ))
    (by simpa using hfg)
  simpa only [completedMap_comp, MonoidHom.comp_apply, ← PositiveDegrees.changeDegreeEquiv_apply]
    using DFunLike.congr_fun h x

end GradedLieHom
end Mei
