/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Basic

/-!
# Change of coefficients for finite KS complexes

A degree-preserving Lie homomorphism changes the wall labels of a finite KS
complex. The labels still belong to the Lie subgroups orthogonal to their whole
wall supports. This operation respects identities, composition and degree
truncation, and sends geometric path products to their images. In particular,
it preserves consistency without requiring injectivity of the coefficient map.

The construction uses `GradedLieHom.truncatedMap`, `LieHom.bchGroupMap` and
`FiniteWallDiagram.relabel`. Its orthogonality argument uses the homogeneous
summands of `orthogonalLieSubalgebra`; it imposes no freeness or finite rank
assumption on the homogeneous pieces.
-/

public section

noncomputable section

namespace Mei.KSComplex

variable {N V R L L' L'' : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  [GradedLieAlgebra ℋ] [IsPositiveGrading d ℋ]
  {C : FinitePolyhedralComplex h} {k l : ℕ}

/-- Apply a fixed-degree Lie homomorphism to the finite wall labels.
The geometric complex and the chosen coorienting degrees are retained. -/
def map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : KSComplex s d ℳ C k where
  isConical := D.isConical
  degree := D.degree
  degree_mem := D.degree_mem
  degree_ne_zero := D.degree_ne_zero
  evaluation_eq_zero := D.evaluation_eq_zero
  label P :=
      (f.truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k)).bchGroupMap
        (D.label P)
  label_mem P := by
    rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
    apply map_orthogonalLieSubalgebra_le (d.truncatedGrading ℒ k)
      (d.truncatedGrading ℳ k) (f.truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k))
      (fun n x hx => by simpa only [PositiveDegreeMap.id_apply] using
        f.truncatedMap_mem k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k) hx) _
    exact (LieSubalgebra.mem_map _ _ _).mpr
      ⟨_, (LieSubalgebra.mem_bchSubgroup _ _).mp (D.label_mem P), rfl⟩

/-- Coefficient change retains the chosen coorienting degrees. -/
@[simp]
theorem map_degree (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.map f).degree = D.degree := (rfl)

/-- Coefficient change applies the induced finite BCH homomorphism to each label. -/
@[simp]
theorem map_label (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (P : C.walls) :
    (D.map f).label P =
      (f.truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k)).bchGroupMap
        (D.label P) := (rfl)

/-- Forgetting the grading identifies coefficient change with ordinary relabelling. -/
@[simp]
theorem toFiniteWallDiagram_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.map f).toFiniteWallDiagram =
      D.toFiniteWallDiagram.relabel
        (f.truncatedMap k (by simp : (PositiveDegreeMap.id d).modulus k ≤ k)).bchGroupMap := by
  ext <;> simp

/-- The identity coefficient map leaves the finite KS complex unchanged. -/
@[simp]
theorem map_id (D : KSComplex s d ℒ C k) : D.map (GradedLieHom.id ℒ) = D := by
  ext P
  · simp
  · simp

/-- Successive coefficient maps compose as equalities of finite KS complexes. -/
@[simp]
theorem map_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.map f).map g =
      D.map (PositiveDegreeMap.comp_id (PositiveDegreeMap.id d) ▸ g.comp f) := by
  ext P
  · simp
  · simp only [map_label, ← MonoidHom.comp_apply, ← LieHom.bchGroupMap_comp]
    congr 2
    apply (d.degreeIdeal ℒ k).lieHom_qext
    intro x
    -- Transporting the composite degree map to the identity does not change its values.
    have hcast {T U : PositiveDegreeMap d d} (e : T = U)
        (u : GradedLieHom T ℒ ℋ) (x : L) : (e ▸ u) x = u x := by
      subst e
      rfl
    simp only [LieHom.comp_apply, LieIdeal.mkQ_apply, GradedLieHom.truncatedMap_mk,
      hcast, GradedLieHom.comp_apply]

/-- Coefficient change commutes with lowering the degree cutoff. -/
@[simp]
theorem truncate_map (D : KSComplex s d ℒ C l)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (hkl : k ≤ l) :
    (D.map f).truncate hkl = (D.truncate hkl).map f := by
  ext P
  · simp
  · simp only [truncate_label, map_label, ← MonoidHom.comp_apply,
      ← LieHom.bchGroupMap_comp]
    congr 2
    apply (d.degreeIdeal ℒ l).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, LieHom.comp_apply]

/-- Fixed-degree coefficient maps preserve consistency. -/
theorem consistent_map (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hD : D.toFiniteWallDiagram.Consistent) : (D.map f).toFiniteWallDiagram.Consistent := by
  rw [toFiniteWallDiagram_map]
  exact hD.relabel _

end Mei.KSComplex
