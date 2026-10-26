/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Basic

/-!
# Coefficient maps of finite KS complexes

A degree-preserving Lie homomorphism maps the labels of a KS complex while
retaining its conical geometry and coorientations. Orthogonal label subgroups
are preserved without injectivity or surjectivity assumptions. The construction
respects identity, composition, cutoff projection and geometric path products,
and sends consistent complexes to consistent complexes.

This uses `GradedLieHom.truncatedMap`, `orthogonalLieSubalgebra`, and the
relabelling API of `FiniteWallDiagram`. It is the coefficient-change construction
for finite conical scattering diagrams; no faithful coefficient action is needed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.KSComplex

variable {N V R L L' L'' : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq N] {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]
  {C : FinitePolyhedralComplex h} {k l : ℕ}

/-- Apply a degree-preserving Lie homomorphism to the wall labels. -/
def map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : KSComplex s d ℳ C k where
  isConical := D.isConical
  degree := D.degree
  degree_mem := D.degree_mem
  degree_ne_zero := D.degree_ne_zero
  evaluation_eq_zero := D.evaluation_eq_zero
  label P := (f.truncatedMap k (by simp)).bchGroupMap (D.label P)
  label_mem P := by
    rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
    apply map_orthogonalLieSubalgebra_le (d.truncatedGrading ℒ k)
      (d.truncatedGrading ℳ k) (f.truncatedMap k (by simp))
      (fun n x hx => by simpa using f.truncatedMap_mem k (by simp) hx)
      (s.evaluation '' (P : Set V))
    exact ⟨BCHGroup.log (D.label P),
      (LieSubalgebra.mem_bchSubgroup _ _).mp (D.label_mem P), rfl⟩

/-- Coefficient change retains coorienting degrees. -/
@[simp]
theorem map_degree (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : (D.map f).degree = D.degree := (rfl)

/-- Each label is mapped by the induced homomorphism of finite BCH groups. -/
@[simp]
theorem map_label (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (P : C.walls) :
    (D.map f).label P = (f.truncatedMap k (by simp)).bchGroupMap (D.label P) := (rfl)

/-- The identity Lie homomorphism leaves a KS complex unchanged. -/
@[simp]
theorem map_id (D : KSComplex s d ℒ C k) : D.map (GradedLieHom.id ℒ) = D := by
  ext P <;> simp

/-- Successive coefficient changes agree with their composite. -/
@[simp]
theorem map_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.map f).map g = D.map
      { toLieHom := g.toLieHom.comp f.toLieHom
        map_mem hx := by simpa using g.map_mem (f.map_mem hx) } := by
  ext P
  · simp
  · simp only [map_label, ← MonoidHom.comp_apply, ← LieHom.bchGroupMap_comp]
    congr 2
    apply (d.degreeIdeal ℒ k).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, ← GradedLieHom.coe_toLieHom]

/-- Forgetting the grading identifies coefficient change with ordinary relabelling. -/
@[simp]
theorem toFiniteWallDiagram_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.map f).toFiniteWallDiagram =
      D.toFiniteWallDiagram.relabel (f.truncatedMap k (by simp)).bchGroupMap := by
  ext <;> simp

/-- Coefficient change preserves consistency, including when some labels become trivial. -/
theorem consistent_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hD : D.toFiniteWallDiagram.Consistent) : (D.map f).toFiniteWallDiagram.Consistent := by
  rw [toFiniteWallDiagram_map]
  exact hD.relabel _

/-- Coefficient change commutes with lowering the degree cutoff. -/
@[simp]
theorem truncate_map (D : KSComplex s d ℒ C l)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (hkl : k ≤ l) :
    (D.map f).truncate hkl = (D.truncate hkl).map f := by
  ext P
  · simp
  · simp only [map_label, truncate_label, ← MonoidHom.comp_apply,
      ← LieHom.bchGroupMap_comp]
    -- Work at the explicit cutoffs rather than transporting quotient types
    -- along the propositional identity-modulus equations.
    congr 2
    apply (d.degreeIdeal ℒ l).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply]

end Mei.KSComplex
