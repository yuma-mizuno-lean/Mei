/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Space
public import Mei.Geometry.ScatteringDiagram.KS.Orthogonal
public import Mei.Geometry.ScatteringDiagram.Finite
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Finite graded Kontsevich–Soibelman complexes

A `KSComplex` decorates an actual finite conical polyhedral complex with positive
degree coorientations and labels in the orthogonal BCH subgroups. Forgetting the
grading gives a finite wall diagram with its geometric path products. Lowering
the degree cutoff preserves the complex and coorientations, projects its labels
and path products, and preserves consistency. The degree point and its negative
are allowed endpoints at every cutoff.

The labeled cone complexes adapt Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), Definition 2.1. The cutoff
maps implement the finite-level transition maps used in Definition 2.3 and
§§2.9–2.11, with orthogonal BCH group labels in place of Lie algebra labels.

The constructions use `FiniteWallDiagram.relabel`,
`orthogonalLieSubalgebra` and its truncation theorem, and Mathlib's
`Module.Dual.finrank_ker_add_one_of_ne_zero`. No salience, saturation or finite
generation of the positive monoid is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (s : KSSpace h) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- A finite conical scattering diagram at a degree cutoff, with orthogonal Lie labels.
The coorienting degree need not be primitive or itself survive the cutoff. -/
structure KSComplex (C : FinitePolyhedralComplex h) (k : ℕ) where
  /-- Every cell is a cone with apex zero; lineality is allowed. -/
  isConical : C.IsConical
  /-- A positive degree specifying each wall's coorientation. -/
  degree : C.walls → N
  /-- Coorienting degrees belong to the allowed monoid. -/
  degree_mem : ∀ P, degree P ∈ d.monoid
  /-- Coorienting degrees are nonzero. -/
  degree_ne_zero : ∀ P, degree P ≠ 0
  /-- The wall lies in the hyperplane of its coorienting degree. -/
  evaluation_eq_zero : ∀ P : C.walls, ∀ θ ∈ (P : Set V), s.evaluation θ (degree P) = 0
  /-- The group label at the retained degree cutoff. -/
  label : C.walls → d.truncatedGroup ℒ k
  /-- The logarithm is supported on degrees annihilating the whole wall. -/
  label_mem : ∀ P : C.walls, label P ∈
    (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
      (s.evaluation '' (P : Set V))).bchSubgroup

namespace KSComplex

variable {s d ℒ} {C : FinitePolyhedralComplex h} {k l m : ℕ}
  (D : KSComplex s d ℒ C k)

/-- The actual wall direction is the kernel of its degree normal. -/
theorem ker_normal (P : C.walls) :
    LinearMap.ker (s.normal (D.degree P)) = (affineSpan ℝ (P : Set V)).direction := by
  let := h.finiteDimensional
  have hle : (affineSpan ℝ (P : Set V)).direction ≤
      LinearMap.ker (s.normal (D.degree P)) := by
    have ha : affineSpan ℝ (P : Set V) ≤
        (LinearMap.ker (s.normal (D.degree P))).toAffineSubspace :=
      affineSpan_le.mpr (fun θ hθ => LinearMap.mem_ker.mpr (by
        simpa only [KSSpace.normal_apply] using D.evaluation_eq_zero P θ hθ))
    simpa using AffineSubspace.direction_le ha
  have hn := s.normal_ne_zero d (D.degree_mem P) (D.degree_ne_zero P)
  have hd := C.finrank_direction_add_one_of_mem_walls P.property
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

/-- Forget the grading while retaining the actual complex, normals and group labels. -/
def toFiniteWallDiagram : FiniteWallDiagram C (d.truncatedGroup ℒ k) where
  normal P := s.normal (D.degree P)
  ker_normal := D.ker_normal
  label := D.label

/-- The underlying coorientation is evaluation at the chosen degree. -/
@[simp]
theorem toFiniteWallDiagram_normal (P : C.walls) :
    D.toFiniteWallDiagram.normal P = s.normal (D.degree P) := (rfl)

/-- Forgetting the grading preserves every label. -/
@[simp]
theorem toFiniteWallDiagram_label (P : C.walls) :
    D.toFiniteWallDiagram.label P = D.label P := (rfl)

/-- Lower the Lie cutoff without changing the geometric complex. -/
def truncate (D : KSComplex s d ℒ C l) (hkl : k ≤ l) : KSComplex s d ℒ C k where
  isConical := D.isConical
  degree := D.degree
  degree_mem := D.degree_mem
  degree_ne_zero := D.degree_ne_zero
  evaluation_eq_zero := D.evaluation_eq_zero
  label P := (d.truncationMap ℒ hkl).bchGroupMap (D.label P)
  label_mem P := by
    rw [← map_bchSubgroup_orthogonalLieSubalgebra ℒ d
      (s.evaluation '' (P : Set V)) hkl]
    exact ⟨D.label P, D.label_mem P, rfl⟩

/-- Truncation retains coorienting degrees. -/
@[simp]
theorem truncate_degree (D : KSComplex s d ℒ C l) (hkl : k ≤ l) :
    (D.truncate hkl).degree = D.degree := (rfl)

/-- Truncation applies the canonical BCH quotient homomorphism to wall labels. -/
@[simp]
theorem truncate_label (D : KSComplex s d ℒ C l) (hkl : k ≤ l) (P : C.walls) :
    (D.truncate hkl).label P = (d.truncationMap ℒ hkl).bchGroupMap (D.label P) := (rfl)

/-- A KS complex is determined by its coorienting degrees and labels. -/
@[ext]
theorem ext {D E : KSComplex s d ℒ C k}
    (hdegree : D.degree = E.degree) (hlabel : D.label = E.label) : D = E := by
  cases D
  cases E
  cases hdegree
  cases hlabel
  rfl

/-- Retaining the same cutoff is the identity. -/
@[simp]
theorem truncate_refl : D.truncate le_rfl = D := by
  ext P
  · rfl
  · simp

/-- Successive cutoff changes compose. -/
@[simp]
theorem truncate_truncate (D : KSComplex s d ℒ C m) (hkl : k ≤ l) (hlm : l ≤ m) :
    (D.truncate hlm).truncate hkl = D.truncate (hkl.trans hlm) := by
  ext P
  · rfl
  · simp only [truncate_label, ← MonoidHom.comp_apply, ← LieHom.bchGroupMap_comp,
      PositiveDegrees.truncationMap_comp]

/-- Forgetting the grading turns cutoff change into ordinary relabelling. -/
@[simp]
theorem toFiniteWallDiagram_truncate (D : KSComplex s d ℒ C l) (hkl : k ≤ l) :
    (D.truncate hkl).toFiniteWallDiagram =
      D.toFiniteWallDiagram.relabel (d.truncationMap ℒ hkl).bchGroupMap := by
  ext <;> simp

/-- Cutoff projections preserve consistency of the actual geometric path products. -/
theorem consistent_truncate (D : KSComplex s d ℒ C l) (hkl : k ≤ l)
    (hD : D.toFiniteWallDiagram.Consistent) :
    (D.truncate hkl).toFiniteWallDiagram.Consistent := by
  rw [toFiniteWallDiagram_truncate]
  exact hD.relabel _

/-- The positive degree point misses every wall, at every cutoff. -/
theorem degreePoint_not_mem (D : KSComplex s d ℒ C k) (P : C.walls) :
    s.degreePoint d ∉ (P : Set V) := by
  intro hP
  have hz : s.normal (D.degree P) (s.degreePoint d) = 0 := by
    simpa only [KSSpace.normal_apply] using D.evaluation_eq_zero P _ hP
  have hp : (0 : ℝ) < d.degree (D.degree P) :=
    Int.cast_pos.mpr (d.degree_pos (D.degree_mem P) (D.degree_ne_zero P))
  exact hp.ne' (by simpa only [KSSpace.normal_apply, KSSpace.evaluation_degreePoint] using hz)

/-- The negative degree point also misses every wall. -/
theorem neg_degreePoint_not_mem (D : KSComplex s d ℒ C k) (P : C.walls) :
    -s.degreePoint d ∉ (P : Set V) := by
  intro hP
  have hp : (0 : ℝ) < d.degree (D.degree P) :=
    Int.cast_pos.mpr (d.degree_pos (D.degree_mem P) (D.degree_ne_zero P))
  have he : s.normal (D.degree P) (-s.degreePoint d) = 0 := by
    simpa only [KSSpace.normal_apply] using D.evaluation_eq_zero P _ hP
  exact hp.ne' (by simpa only [map_neg, KSSpace.normal_apply,
    KSSpace.evaluation_degreePoint, neg_eq_zero] using he)

end KSComplex
end Mei
