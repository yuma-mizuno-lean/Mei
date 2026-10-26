/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Basic

/-!
# Degree-preserving maps of finite KS diagrams

A degree-preserving Lie homomorphism maps finite KS diagrams by applying its
finite BCH homomorphism to every wall label. Orthogonal label subgroups are
preserved, so the result is again a KS diagram on the same geometric complex.
This operation respects identity, composition and degree truncation. Every
geometric path product is mapped by the same BCH homomorphism; in particular,
consistency is preserved.

The construction uses `GradedLieHom.truncatedMap`, `LieHom.bchGroupMap` and
`FiniteWallDiagram.relabel`. It realizes finite-order change of Lie coefficients
in the sense of Bridgeland, *Scattering diagrams, Hall algebras and stability
conditions*, §2.11 ([arXiv:1603.00416](https://arxiv.org/abs/1603.00416)).
-/

public section

noncomputable section

namespace Mei.KSComplex

universe u

variable {N V R : Type*} {L L' L'' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  {C : FinitePolyhedralComplex h} {k l : ℕ}

/-- Map the Lie coefficients of a finite KS diagram, retaining all wall geometry
and coorienting degrees. Identity labels created by the map are retained. -/
def map (D : KSComplex s d ℒ C k) (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    KSComplex s d ℳ C k where
  isConical := D.isConical
  degree := D.degree
  degree_mem := D.degree_mem
  degree_ne_zero := D.degree_ne_zero
  evaluation_eq_zero := D.evaluation_eq_zero
  label P := (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.label P)
  label_mem P := by
    rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
    exact map_mem_orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
      (d.truncatedGrading ℳ k)
      (f.truncatedMap (a := k) k (by simp)).toLinearMap.toAddMonoidHom
      (fun _ _ hx => by
        simpa only [LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
          PositiveDegreeMap.id_apply] using
          f.truncatedMap_mem k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k) hx)
      ((LieSubalgebra.mem_bchSubgroup _ _).mp (D.label_mem P))

/-- Changing Lie coefficients retains the coorienting degrees. -/
@[simp]
theorem map_degree (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : (D.map f).degree = D.degree := (rfl)

/-- The mapped label is the image under the finite BCH homomorphism. -/
@[simp]
theorem map_label (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (P : C.walls) :
    (D.map f).label P = (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.label P) := (rfl)

/-- Changing coefficients by the identity leaves the diagram unchanged. -/
@[simp]
theorem map_id (D : KSComplex s d ℒ C k) : D.map (GradedLieHom.id ℒ) = D := by
  ext P
  · simp only [map_degree]
  · simp

/-- Successive coefficient maps agree with their composite Lie homomorphism. -/
@[simp]
theorem map_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.map f).map g = D.map
      { toLieHom := (g.comp f).toLieHom
        map_mem := fun hx => by simpa using (g.comp f).map_mem hx } := by
  ext P
  · simp only [map_degree]
  · simp only [map_label]
    -- Rebundle the composite at the identity degree map, since the generic
    -- composition carries the propositionally equal composite of identity maps.
    have he : (GradedLieHom.mk (g.comp f).toLieHom
        (fun hx => by simpa using (g.comp f).map_mem hx) :
        GradedLieHom (PositiveDegreeMap.id d) ℒ ℋ).truncatedMap (a := k) k (by simp) =
        (g.truncatedMap (a := k) k (by simp)).comp
          (f.truncatedMap (a := k) k (by simp)) := by
      apply (d.degreeIdeal ℒ k).lieHom_qext
      intro x
      simp only [LieIdeal.mkQ_apply, LieHom.comp_apply, GradedLieHom.truncatedMap_mk,
        GradedLieHom.mk_apply, GradedLieHom.coe_toLieHom, GradedLieHom.comp_apply]
    rw [he, LieHom.bchGroupMap_comp, MonoidHom.comp_apply]

/-- Forgetting the grading turns coefficient change into group relabelling. -/
@[simp]
theorem toFiniteWallDiagram_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.map f).toFiniteWallDiagram =
      D.toFiniteWallDiagram.relabel (f.truncatedMap (a := k) k (by simp)).bchGroupMap := by
  ext <;> simp

/-- Change of Lie coefficients preserves consistency. -/
theorem consistent_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hD : D.toFiniteWallDiagram.Consistent) : (D.map f).toFiniteWallDiagram.Consistent := by
  rw [toFiniteWallDiagram_map]
  exact hD.relabel _

/-- Lowering the order and changing Lie coefficients commute as actual diagrams. -/
@[simp]
theorem truncate_map (D : KSComplex s d ℒ C l)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (hkl : k ≤ l) :
    (D.map f).truncate hkl = (D.truncate hkl).map f := by
  ext P
  · simp only [map_degree, truncate_degree]
  · simp only [truncate_label, map_label]
    have ht : (d.truncationMap ℳ hkl).comp
        (f.truncatedMap (a := l) l (by simp)) =
        (f.truncatedMap (a := k) k (by simp)).comp (d.truncationMap ℒ hkl) := by
      apply (d.degreeIdeal ℒ l).lieHom_qext
      intro x
      simp [LieIdeal.mkQ_apply]
    have he := congrArg (fun q => q.bchGroupMap) ht
    simp only [LieHom.bchGroupMap_comp] at he
    exact DFunLike.congr_fun he (D.label P)

end Mei.KSComplex
