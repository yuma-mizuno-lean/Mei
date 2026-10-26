/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision

/-!
# Ambient complexes adapted to directed diagrams

At each cutoff, choose a finite rational-normal complex covering the ambient
space whose walls subdivide every active directed support. On the relative
interior of each cell, membership in each active support is constant: meeting
that support forces the entire closed cell to lie in it. Increasing the cutoff
subdivides the earlier complex. These are the geometric carriers on which one
can assign chamber lifts and crossing defects.

The construction applies `FinitePolyhedralComplex.ambientSubdivision` to fixed
presentations of the indexed supports. Its wall coverage uses the supporting
hyperplane through a relative interior point and then closedness at boundary
points. Presentations are auxiliary choices; the public interface concerns
actual cells and supports. Repeated walls, lineality, arbitrary real offsets
and vanishing spatial degree directions are allowed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

private def presentation (j : ι) : RationalAffinePolyhedron h :=
  Classical.choose (isRationalNormalPolyhedron_iff.mp (D.wall j).rational_support)

private theorem presentation_carrier (j : ι) :
    (D.presentation j).carrier = (D.wall j).support :=
  Classical.choose_spec (isRationalNormalPolyhedron_iff.mp (D.wall j).rational_support)

/-- A full ambient complex adapted to the active supports at one cutoff. Each
indexed support has a fixed presentation, used at every cutoff where it is active. -/
def adaptedComplex (k : ℕ) : FinitePolyhedralComplex h :=
  FinitePolyhedralComplex.ambientSubdivision (fun j : D.active k => D.presentation j.val)

/-- The adapted complex covers the entire ambient space. -/
@[simp]
theorem support_adaptedComplex (k : ℕ) : (D.adaptedComplex k).support = univ := by
  unfold adaptedComplex
  exact FinitePolyhedralComplex.support_ambientSubdivision _

/-- Every point of an active support lies on an adapted wall contained in that
support, even when the point is on the support's relative boundary. -/
theorem exists_mem_adaptedComplex_walls_subset (k : ℕ) (j : D.active k)
    {x : V} (hx : x ∈ (D.wall j).support) :
    ∃ Q ∈ (D.adaptedComplex k).walls, x ∈ Q ∧ Q ⊆ (D.wall j).support := by
  have hdim : Module.finrank ℝ (affineSpan ℝ (D.presentation j.val).carrier).direction + 1 =
      Module.finrank ℝ V := by
    rw [D.presentation_carrier]
    exact (D.wall j).finrank_direction_add_one
  have hxP : x ∈ (D.presentation j.val).carrier := by
    rw [D.presentation_carrier]
    exact hx
  have he := FinitePolyhedralComplex.exists_mem_ambientSubdivision_walls_subset
    (fun a : D.active k => D.presentation a.val) j hdim hxP
  rw [D.presentation_carrier] at he
  exact he

/-- An active support is the union of the adapted walls contained in it. -/
theorem support_eq_iUnion_adaptedComplex_walls (k : ℕ) (j : D.active k) :
    (D.wall j).support = ⋃ (Q : Set V) (_ : Q ∈ (D.adaptedComplex k).walls)
      (_ : Q ⊆ (D.wall j).support), Q := by
  have hdim : Module.finrank ℝ (affineSpan ℝ (D.presentation j.val).carrier).direction + 1 =
      Module.finrank ℝ V := by
    rw [D.presentation_carrier]
    exact (D.wall j).finrank_direction_add_one
  have he := FinitePolyhedralComplex.carrier_eq_iUnion_ambientSubdivision_walls
    (fun a : D.active k => D.presentation a.val) j hdim
  rw [D.presentation_carrier] at he
  exact he

/-- On a cell's relative interior, meeting an active support is equivalent to
containment of the whole closed cell in that support. -/
theorem mem_support_iff_of_mem_intrinsicInterior_adaptedComplex (k : ℕ)
    {Q : Set V} (hQ : Q ∈ (D.adaptedComplex k).cells) {x : V}
    (hx : x ∈ intrinsicInterior ℝ Q) (j : D.active k) :
    x ∈ (D.wall j).support ↔ Q ⊆ (D.wall j).support := by
  rw [← D.presentation_carrier j.val]
  constructor
  · exact FinitePolyhedralComplex.subset_carrier_of_mem_intrinsicInterior_ambientSubdivision
      _ hQ j hx
  · exact fun hsub => hsub (intrinsicInterior_subset hx)

/-- Raising the cutoff gives a subdivision of the earlier adapted complex. -/
theorem adaptedComplex_isSubdivision {k l : ℕ} (hkl : k ≤ l) :
    (D.adaptedComplex l).IsSubdivision (D.adaptedComplex k) :=
  FinitePolyhedralComplex.ambientSubdivision_isSubdivision_comp
    (fun j : D.active l => D.presentation j.val) (Set.inclusion (D.active_mono hkl))

end Mei.DirectedDiagram
