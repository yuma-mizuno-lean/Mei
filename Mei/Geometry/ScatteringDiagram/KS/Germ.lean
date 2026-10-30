/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Germ
public import Mei.Geometry.ScatteringDiagram.KS.Equivalence

/-!
# Local compatibility of KS labels

Equivalence identifies labels at common regular wall points, independently of
consistency. All KS coorientations are positive on the degree point, so their
local labels compare without a sign choice. A regular wall point absent from an
equivalent diagram has identity label.

In a completed diagram, these statements identify the projected labels at
any two cutoffs even when the underlying complexes are unrelated. They also
show that a higher-order wall absent at a lower cutoff has trivial
projection there. This is the local compatibility needed to assemble indexed
representatives from finite KS labels.

The argument uses `FiniteWallDiagram.Equivalent.label_eq` and
`FiniteWallDiagram.Equivalent.label_eq_one`, together with
`KSSpace.evaluation_degreePoint_pos`. It follows the regular-wall test in
Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
Definition 2.3 and §§2.9–2.11 (arXiv:1603.00416v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

namespace KSComplex

variable {C C' : FinitePolyhedralComplex h} {k : ℕ}
  (D : KSComplex s d ℒ C k) (E : KSComplex s d ℒ C' k)

/-- Equivalent KS complexes have equal labels at common regular wall points.
The supported rays and coorienting degrees need not be chosen identically. -/
theorem label_eq_of_equivalent
    (hDE : D.toFiniteWallDiagram.Equivalent E.toFiniteWallDiagram)
    (P : C.walls) (Q : C'.walls) {θ : V}
    (hθP : θ ∈ (P : Set V)) (hθQ : θ ∈ (Q : Set V))
    (hθD : θ ∉ singularSupport (fun S : C.walls => (S : Set V)))
    (hθE : θ ∉ singularSupport (fun S : C'.walls => (S : Set V))) :
    D.label P = E.label Q := by
  have hposD : 0 < D.toFiniteWallDiagram.normal P (s.degreePoint d) := by
    simpa only [toFiniteWallDiagram_normal, KSSpace.normal_apply] using
      s.evaluation_degreePoint_pos d (D.degree_mem P) (D.degree_ne_zero P)
  have hposE : 0 < E.toFiniteWallDiagram.normal Q (s.degreePoint d) := by
    simpa only [toFiniteWallDiagram_normal, KSSpace.normal_apply] using
      s.evaluation_degreePoint_pos d (E.degree_mem Q) (E.degree_ne_zero Q)
  simpa only [toFiniteWallDiagram_label] using
    hDE.label_eq P Q hθP hθQ hθD hθE hposD hposE

/-- A regular KS wall missing from an equivalent complex has identity label. -/
theorem label_eq_one_of_equivalent
    (hDE : D.toFiniteWallDiagram.Equivalent E.toFiniteWallDiagram)
    (P : C.walls) {θ : V} (hθP : θ ∈ (P : Set V))
    (hθD : θ ∉ singularSupport (fun S : C.walls => (S : Set V)))
    (hθE : ∀ Q : C'.walls, θ ∉ (Q : Set V)) : D.label P = 1 := by
  simpa only [toFiniteWallDiagram_label] using
    hDE.label_eq_one P hθP hθD hθE

end KSComplex

namespace CompletedDiagram

variable {C : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- Labels at common regular wall points in any two levels agree after
projection, without a consistency assumption. -/
theorem truncation_label_eq {k l : ℕ} (hkl : k ≤ l)
    (P : (C k).walls) (Q : (C l).walls) {θ : V}
    (hθP : θ ∈ (P : Set V)) (hθQ : θ ∈ (Q : Set V))
    (hθP_reg : θ ∉ singularSupport (fun S : (C k).walls => (S : Set V)))
    (hθQ_reg : θ ∉ singularSupport (fun S : (C l).walls => (S : Set V))) :
    (d.truncationMap ℒ hkl).bchGroupMap ((D.diagram l).label Q) =
      (D.diagram k).label P := by
  simpa only [KSComplex.truncate_label] using
    KSComplex.label_eq_of_equivalent _ _ (D.truncate_equivalent hkl)
      Q P hθQ hθP hθQ_reg hθP_reg

/-- A higher-order wall absent at a point of a lower-order wall family has
identity projected label there. The higher-order point must be regular. -/
theorem truncation_label_eq_one {k l : ℕ} (hkl : k ≤ l)
    (Q : (C l).walls) {θ : V} (hθQ : θ ∈ (Q : Set V))
    (hθQ_reg : θ ∉ singularSupport (fun S : (C l).walls => (S : Set V)))
    (hθP : ∀ P : (C k).walls, θ ∉ (P : Set V)) :
    (d.truncationMap ℒ hkl).bchGroupMap ((D.diagram l).label Q) = 1 := by
  simpa only [KSComplex.truncate_label] using
    KSComplex.label_eq_one_of_equivalent _ _ (D.truncate_equivalent hkl) Q hθQ hθQ_reg hθP

end CompletedDiagram
end Mei
