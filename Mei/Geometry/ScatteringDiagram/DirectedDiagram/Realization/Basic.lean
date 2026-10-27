/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.CellCrossing
public import Mei.Geometry.ScatteringDiagram.Finite

/-!
# Realizing directed transport on an adapted complex

The combined labels on the walls of an adapted complex define a finite wall
diagram with exactly the original directed transport. Artificial cuts contribute
identity factors, and a crossing of coincident indexed supports contributes their
combined label. Thus geometric paths on the adapted complex compute the actual
finite-order products, without a consistency assumption.

The label stored by `FiniteWallDiagram` is the inverse of `wallCrossingLabel`:
the latter already describes a positive crossing, whereas the former is inverted
on a positive crossing. The comparison combines `adaptedPathPrefunctor`,
`crossingEventProduct_eq_combinedLabel`, and
`WallComplement.segmentPathProduct_eq_prod_of_crossingTimes`. This supplies the
passage from indexed supports to cellwise transport used in the central-defect
construction of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, proof of Theorem 2.6. Unbounded supports, lineality, real offsets
and repeated indexed walls are allowed.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  (k : ℕ) (ν : (D.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ Q, (ν Q).ker = (affineSpan ℝ (Q : Set V)).direction)

/-- The finite wall diagram obtained by merging the indexed labels on each
adapted wall cell. Its stored labels are inverted on positive crossings. -/
def adaptedDiagram : FiniteWallDiagram (D.adaptedComplex k) (d.truncatedGroup ℒ k) where
  normal := ν
  ker_normal := hν
  label Q := (D.wallCrossingLabel Q (ν Q) (hν Q))⁻¹

@[simp]
theorem adaptedDiagram_normal (Q : (D.adaptedComplex k).walls) :
    (D.adaptedDiagram k ν hν).normal Q = ν Q := (rfl)

/-- The stored label is the inverse of the factor for a positive crossing. -/
@[simp]
theorem adaptedDiagram_label (Q : (D.adaptedComplex k).walls) :
    (D.adaptedDiagram k ν hν).label Q = (D.wallCrossingLabel Q (ν Q) (hν Q))⁻¹ := (rfl)

variable {k} {x y : WallComplement (fun Q : (D.adaptedComplex k).walls => (Q : Set V))}

private theorem eventProduct_eq_adapted_factor (e : x ⟶ y)
    {a : (D.adaptedComplex k).walls × ℝ}
    (ha : a ∈ (D.adaptedComplex k).orderedCrossings e) :
    crossingEventProduct (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => CompletedGroup.projection k (D.wall j).label)
        (D.activeLabels_commute k) ((D.adaptedPathPrefunctor k).map e) a.2 =
      if 0 < ν a.1 (y.val - x.val) then
        ((D.adaptedDiagram k ν hν).label a.1)⁻¹
      else (D.adaptedDiagram k ν hν).label a.1 := by
  have hcross := (mem_crossings x y a.1 a.2).mp
    (((D.adaptedComplex k).mem_orderedCrossings e a).mp ha)
  have hq := (e.down.crossing_mem_intrinsicInterior hcross.1 hcross.2).2
  rw [D.crossingEventProduct_eq_combinedLabel k _ hcross.1]
  simp only [D.adaptedPathPrefunctor_obj_val, adaptedDiagram_label]
  have hn := (D.adaptedComplex k).normal_velocity_ne_zero (ν a.1) e ha (hν a.1)
  split_ifs with hv
  · rw [inv_inv, D.wallCrossingLabel_eq_combinedLabel a.1 (ν a.1) (hν a.1) hq hv]
  · have hpos : 0 < (-ν a.1) (y.val - x.val) := by
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hv) hn)
    rw [← D.wallCrossingLabel_eq_combinedLabel a.1 (-ν a.1) (by simpa using hν a.1)
      hq hpos, D.wallCrossingLabel_neg]

/-- On a segment, directed transport equals the product of the combined labels
on its successive adapted wall crossings. Extra artificial cuts are harmless. -/
theorem levelPathProduct_toPath_eq_adaptedDiagram (e : x ⟶ y) :
    D.levelPathProduct k (((D.adaptedPathPrefunctor k).map e).toPath) =
      (D.adaptedDiagram k ν hν).pathProduct e.toPath := by
  let F := D.adaptedPathPrefunctor k
  let T := ((D.adaptedComplex k).orderedCrossings e).map Prod.snd
  have hT : T.Pairwise (· < ·) :=
    List.pairwise_map.mpr ((D.adaptedComplex k).pairwise_orderedCrossings e)
  have hcover : ∀ t ∈ orderedCrossingTimes (F.map e), t ∈ T := by
    intro t ht
    obtain ⟨j, hj⟩ := (mem_orderedCrossingTimes (F.map e) t).mp ht
    obtain ⟨htI, hj⟩ := (mem_crossings (F.obj x) (F.obj y) j t).mp hj
    obtain ⟨Q, hQ, hq, -⟩ := D.exists_mem_adaptedComplex_walls_subset k j hj
    simp only [F, D.adaptedPathPrefunctor_obj_val] at hq
    exact List.mem_map.mpr ⟨(⟨Q, hQ⟩, t),
      ((D.adaptedComplex k).mem_orderedCrossings e _).mpr
        ((mem_crossings x y _ t).mpr ⟨htI, hq⟩), rfl⟩
  rw [D.levelPathProduct_eq_wallPathProduct k _ (D.activeLabels_commute k),
    Quiver.Path.wallPathProduct_toPath,
    segmentPathProduct_eq_prod_of_crossingTimes _ _ _ (F.map e) T hT hcover,
    FiniteWallDiagram.pathProduct_toPath]
  simp only [T, List.map_reverse, List.map_map, Function.comp_def, adaptedDiagram_normal]
  apply congrArg (fun l : List (d.truncatedGroup ℒ k) => l.reverse.prod)
  apply List.map_congr_left
  intro a ha
  exact D.eventProduct_eq_adapted_factor ν hν e ha

/-- Every admissible path through the adapted complex computes the original
directed transport, including all coincident indexed contributions. -/
theorem levelPathProduct_eq_adaptedDiagram (p : AdmissiblePLPath x y) :
    D.levelPathProduct k ((D.adaptedPathPrefunctor k).mapPath p) =
      (D.adaptedDiagram k ν hν).pathProduct p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, ← Quiver.Path.comp_toPath_eq_cons,
      D.levelPathProduct_comp, ih, D.levelPathProduct_toPath_eq_adaptedDiagram ν hν e,
      FiniteWallDiagram.pathProduct_cons]

end Mei.DirectedDiagram
