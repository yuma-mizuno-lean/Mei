/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Completion

/-!
# Rank-one reconstruction is a single labelled wall

For any positive grading indexed by `ℤ`, every wall of a bounded-degree arrangement is
`{0}`, and its reconstructed label is the projection of the original completed
group element. A wall occurs exactly when a nonzero allowed degree survives the
cutoff. For the standard nonnegative grading, reconstruction is therefore the single
wall at the origin carrying the original completed label: the wall occurs at every
positive cutoff, and at order zero there are no walls.

This applies in particular to the nonabelian graded Heisenberg algebra: the
geometry has one wall, but its labels need not commute. No abelian-ray hypothesis
is imposed. The construction is the specialization of Bridgeland's reconstruction
(*Scattering diagrams, Hall algebras and stability conditions*, §§3.2–3.4) already
formalized by `PositiveDegrees.reconstruct`. The proof uses the uniqueness of
`PositiveDegrees.signFactorizationEquiv` in its uniform-sign form.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {V R L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : ℤ →+ V} (d : PositiveDegrees ℤ) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  (ℒ : ℤ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {k : ℕ}

/-- In rank one, the reconstructed wall carries the original completed label,
read through its cutoff projections.
This also applies when the positive monoid omits its primitive ray generator. -/
@[simp↓]
theorem reconstruct_label_int (g : d.completedBCHGroup ℒ)
    (P : (d.arrangementComplex h k).walls) :
    ((d.reconstruct h ℒ g).diagram k).label P = CompletedGroup.projection k g := by
  have hP : (P : Set (V →L[ℝ] ℝ)) = {0} :=
    d.eq_singleton_zero_of_mem_arrangementComplex_walls_int h P.property
  have hzero : (0 : V →L[ℝ] ℝ) ∈ intrinsicInterior ℝ (P : Set (V →L[ℝ] ℝ)) := by
    simp [hP]
  rw [d.reconstruct_diagram]
  let a : d.truncatedGroup ℒ k := CompletedGroup.projection k g
  -- The tower projection has the concrete truncated BCH carrier; naming it
  -- fixes that identification before applying the finite reconstruction API.
  change (d.reconstructFinite h ℒ a).label P = a
  rw [d.reconstructFinite_label h ℒ a P hzero]
  have hf := d.signFactorizationEquiv_symm_of_uniformSign_monoid ℒ
    ((0 : V →L[ℝ] ℝ).toAddMonoidHom.comp i) 0 (by intros; simp)
    a 0
  simpa using hf

end Mei.PositiveDegrees
