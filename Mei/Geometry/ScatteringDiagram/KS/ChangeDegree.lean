/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Class
public import Mei.Algebra.Lie.BCH.ChangeDegree

/-!
# Changing degree on consistent diagram classes

Two positive degree functions on the same positive monoid give equivalent spaces of
consistent KS diagram classes. The comparison passes through chamber transport,
changes the filtration of the completed BCH group, and reconstructs. It therefore
acts on classes without choosing a common sequence of complexes for the two filtrations.

The comparison respects identity, inverses and composition and commutes with coefficient
maps. Its finite projections use the actual cutoff modulus of the group comparison.
The construction combines `PositiveDegrees.reconstructionEquiv` with
`PositiveDegrees.changeDegreeEquiv`; no finiteness assumption on generators of the
positive monoid is needed.
-/

public section

noncomputable section

universe u

namespace Mei.ConsistentDiagram.Class

variable {N V R : Type*} {L L' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  {i : N →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (d e p : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [IsPositiveGrading e ℒ]
  [IsPositiveGrading p ℒ]

/-- Change degree on consistent diagram classes by classifying, changing the completed
group filtration, and reconstructing. This does not change arbitrary inconsistent diagrams. -/
def changeDegreeEquiv (hP : d.monoid = e.monoid) :
    Class (s := KSSpace.continuousDual h) (d := d) (ℒ := ℒ) ≃
      Class (s := KSSpace.continuousDual h) (d := e) (ℒ := ℒ) :=
  (d.reconstructionEquiv h ℒ).trans
    ((d.changeDegreeEquiv e ℒ hP).toEquiv.trans (e.reconstructionEquiv h ℒ).symm)

/-- The class comparison has the changed completed chamber transport. -/
@[simp]
theorem chamberTransport_changeDegreeEquiv (hP : d.monoid = e.monoid)
    (x : Class (s := KSSpace.continuousDual h) (d := d) (ℒ := ℒ)) :
    (changeDegreeEquiv h d e ℒ hP x).chamberTransport =
      d.changeDegreeEquiv e ℒ hP x.chamberTransport := by
  rw [← e.reconstructionEquiv_apply h ℒ]
  simp only [changeDegreeEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    PositiveDegrees.reconstructionEquiv_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]

/-- Changing to the same degree function leaves the diagram class unchanged. -/
@[simp]
theorem changeDegreeEquiv_refl :
    changeDegreeEquiv h d d ℒ rfl = Equiv.refl _ := by
  ext x
  apply chamberTransport_injective
  simp

/-- Reversing the change of degree gives the inverse comparison on classes. -/
@[simp]
theorem changeDegreeEquiv_symm (hP : d.monoid = e.monoid) :
    (changeDegreeEquiv h d e ℒ hP).symm = changeDegreeEquiv h e d ℒ hP.symm := by
  apply Equiv.symm_eq_iff_trans_eq_refl.mpr
  ext x
  apply chamberTransport_injective
  simp only [Equiv.trans_apply, chamberTransport_changeDegreeEquiv]
  rw [← PositiveDegrees.changeDegreeEquiv_symm]
  exact (d.changeDegreeEquiv e ℒ hP).symm_apply_apply _

/-- Successive degree changes equal the direct comparison, independently of the
intermediate cutoff modulus. -/
@[simp]
theorem changeDegreeEquiv_trans (hde : d.monoid = e.monoid) (hep : e.monoid = p.monoid) :
    (changeDegreeEquiv h d e ℒ hde).trans (changeDegreeEquiv h e p ℒ hep) =
      changeDegreeEquiv h d p ℒ (hde.trans hep) := by
  ext x
  apply chamberTransport_injective
  simpa only [Equiv.trans_apply, chamberTransport_changeDegreeEquiv, MulEquiv.trans_apply] using
    congrArg (fun f : d.completedBCHGroup ℒ ≃* p.completedBCHGroup ℒ => f x.chamberTransport)
      (d.changeDegreeEquiv_trans e p ℒ hde hep)

/-- Changing degree carries the class of a reconstruction to the reconstruction of
the changed group element. -/
@[simp]
theorem changeDegreeEquiv_reconstructionEquiv_symm (hP : d.monoid = e.monoid)
    (g : d.completedBCHGroup ℒ) :
    changeDegreeEquiv h d e ℒ hP ((d.reconstructionEquiv h ℒ).symm g) =
      (e.reconstructionEquiv h ℒ).symm (d.changeDegreeEquiv e ℒ hP g) := by
  exact congrArg (e.reconstructionEquiv h ℒ).symm
    (congrArg (d.changeDegreeEquiv e ℒ hP) ((d.reconstructionEquiv h ℒ).apply_symm_apply g))

variable {ℳ : N → Submodule R L'} [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℳ] [IsPositiveGrading e ℳ]

/-- Degree change commutes with coefficient change on consistent classes. The two
coefficient maps need only have the same underlying Lie homomorphism. -/
theorem changeDegreeEquiv_map (hP : d.monoid = e.monoid)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id e) ℒ ℳ)
    (hfg : f.toLieHom = g.toLieHom)
    (x : Class (s := KSSpace.continuousDual h) (d := d) (ℒ := ℒ)) :
    changeDegreeEquiv h d e ℳ hP (map f x) =
      map g (changeDegreeEquiv h d e ℒ hP x) := by
  apply chamberTransport_injective
  simp only [chamberTransport_changeDegreeEquiv, chamberTransport_map]
  exact GradedLieHom.changeDegreeEquiv_naturality hP hP f g hfg x.chamberTransport

end Mei.ConsistentDiagram.Class
