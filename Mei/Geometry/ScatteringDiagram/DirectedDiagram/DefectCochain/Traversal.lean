/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.DefectCochain.Independence
public import Mei.Geometry.Convex.PolyhedralComplex.Traversal

/-!
# Crossing defects along actual single-crossing segments

A positive segment crossing one adapted wall has its original endpoints in the
stored source and target chambers of that wall. Viewed as a segment through the
active directed supports, its product is the stored crossing label. Consequently
the existing `AdaptedWallCrossing.coe_defect` formula applies to the actual
segment product and the chamber lifts at its endpoints. No shortness hypothesis
or consistency at the crossing order is needed.

The chamber comparison uses
`FinitePolyhedralComplex.exists_chambers_of_crossings_singleton` and
`AdaptedWallCrossing.eventually_mem_interiors`. The product comparison uses
`DirectedDiagram.exists_mem_adaptedComplex_walls_subset` to recover every active
crossing, including simultaneous coincident walls, and then
`DirectedDiagram.levelPathProduct_toPath_eq_combinedLabel`.
This is the passage from geometric crossings to central crossing coefficients
in the obstruction argument of Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, proof of Theorem 2.6.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram.AdaptedWallCrossing

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {D : DirectedDiagram (d := d) h H ι}
  {l : ℕ} {σ : OrientedCell h 1}
  {hσ : σ.carrier ∈ (D.adaptedComplex l).walls}
  (c : D.AdaptedWallCrossing σ hσ)
  {x y : WallComplement (fun W : (D.adaptedComplex l).walls => (W : Set V))}

/-- The original endpoints of a positive single-crossing segment lie in the
stored incident chambers, even when the segment is not short. -/
theorem mem_interiors_of_crossings_singleton (e : x ⟶ y) (t : ℝ)
    (he : crossings x y = {(⟨σ.carrier, hσ⟩, t)})
    (hv : 0 < h.realCharacter c.normal (y.val - x.val)) :
    x.val ∈ interior (c.minus : Set V) ∧ y.val ∈ interior (c.plus : Set V) := by
  have hm : (⟨σ.carrier, hσ⟩, t) ∈ crossings x y := by rw [he]; exact mem_singleton _
  obtain ⟨ht, hmem⟩ := (mem_crossings x y _ t).mp hm
  obtain ⟨ht', hri⟩ := e.down.crossing_mem_intrinsicInterior ht hmem
  obtain ⟨P, hP, Q, hQ, -, -, hbefore, hafter⟩ :=
    (D.adaptedComplex l).exists_chambers_of_crossings_singleton e ⟨σ.carrier, hσ⟩ t he
      (by simp only [D.support_adaptedComplex, interior_univ, mem_univ])
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ∈ Ioo 0 (min t (1 - t)) :=
    Ioo_mem_nhdsGT (lt_min ht'.1 (sub_pos.mpr ht'.2))
  obtain ⟨a, ha, hc⟩ := (hsmall.and (c.eventually_mem_interiors hri hv)).exists
  have hb : AffineMap.lineMap x.val y.val t - a • (y.val - x.val) ∈ interior P := by
    have hb := hbefore (t - a) ⟨by linarith [ha.2.trans_le (min_le_left _ _)],
      by linarith [ha.1]⟩
    simpa only [AffineMap.lineMap_apply_module', sub_smul, sub_eq_add_neg, add_smul,
      neg_smul, add_assoc, add_left_comm, add_comm] using hb
  have haQ : AffineMap.lineMap x.val y.val t + a • (y.val - x.val) ∈ interior Q := by
    have haQ := hafter (t + a) ⟨by linarith [ha.1],
      by linarith [ha.2.trans_le (min_le_right _ _)]⟩
    simpa only [AffineMap.lineMap_apply_module', add_smul, add_assoc,
      add_left_comm, add_comm] using haQ
  have hPm : P = (c.minus : Set V) := (D.adaptedComplex l).eq_of_mem_intrinsicInterior
    (((D.adaptedComplex l).mem_cellsOfCodimension 0 P).mp hP).1
    (((D.adaptedComplex l).mem_cellsOfCodimension 0 _).mp c.minus.property).1
    (interior_subset_intrinsicInterior hb) (interior_subset_intrinsicInterior hc.1)
  have hQp : Q = (c.plus : Set V) := (D.adaptedComplex l).eq_of_mem_intrinsicInterior
    (((D.adaptedComplex l).mem_cellsOfCodimension 0 Q).mp hQ).1
    (((D.adaptedComplex l).mem_cellsOfCodimension 0 _).mp c.plus.property).1
    (interior_subset_intrinsicInterior haQ) (interior_subset_intrinsicInterior hc.2)
  constructor
  · simpa only [AffineMap.lineMap_apply_zero, hPm] using hbefore 0 ⟨le_rfl, ht'.1⟩
  · simpa only [AffineMap.lineMap_apply_one, hQp] using hafter 1 ⟨ht'.2, le_rfl⟩

/-- On the same geometric segment through the active supports, the actual
directed transport is the stored positive crossing label. A single adapted
wall crossing may account for several coincident active directed walls. -/
theorem levelPathProduct_eq_label_of_crossings_singleton (e : x ⟶ y) (t : ℝ)
    (he : crossings x y = {(⟨σ.carrier, hσ⟩, t)})
    (hv : 0 < h.realCharacter c.normal (y.val - x.val))
    {x' y' : WallComplement (fun j : D.active l => (D.wall j).support)}
    (e' : x' ⟶ y') (hx : x'.val = x.val) (hy : y'.val = y.val) :
    D.levelPathProduct l e'.toPath =
      D.wallCrossingLabel ⟨σ.carrier, hσ⟩ (h.realCharacter c.normal) c.ker_normal := by
  have hm : (⟨σ.carrier, hσ⟩, t) ∈ crossings x y := by rw [he]; exact mem_singleton _
  obtain ⟨ht, hmem⟩ := (mem_crossings x y _ t).mp hm
  have hri := (e.down.crossing_mem_intrinsicInterior ht hmem).2
  have hcross (j : D.active l) (u : ℝ) : (j, u) ∈ crossings x' y' ↔
      AffineMap.lineMap x.val y.val t ∈ (D.wall j).support ∧ u = t := by
    constructor
    · intro hj
      obtain ⟨hu, hj⟩ := (mem_crossings x' y' j u).mp hj
      rw [hx, hy] at hj
      obtain ⟨W, hW, hz, -⟩ := D.exists_mem_adaptedComplex_walls_subset l j hj
      have hWu := (mem_crossings x y ⟨W, hW⟩ u).mpr ⟨hu, hz⟩
      rw [he, Set.mem_singleton_iff, Prod.mk.injEq] at hWu
      exact ⟨hWu.2 ▸ hj, hWu.2⟩
    · rintro ⟨hj, hu⟩
      subst u
      exact (mem_crossings x' y' j t).mpr ⟨ht, by simpa only [hx, hy] using hj⟩
  rw [D.levelPathProduct_toPath_eq_combinedLabel l e'
    (AffineMap.lineMap x.val y.val t)
    (D.notMem_singularSupport_of_mem_intrinsicInterior_adaptedWall hσ hri) t hcross]
  rw [hx, hy]
  exact (D.wallCrossingLabel_eq_combinedLabel ⟨σ.carrier, hσ⟩
    (h.realCharacter c.normal) c.ker_normal hri hv).symm

end Mei.DirectedDiagram.AdaptedWallCrossing
