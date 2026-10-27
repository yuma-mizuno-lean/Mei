/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing
public import Mei.Geometry.Convex.Polyhedron.Path.Comparison

/-!
# Combined wall labels under directed equivalence

Finite-order equivalence identifies the signed combined labels at every common
regular point, in every direction transverse to the incident walls. More generally,
labels formed at two possibly different higher cutoffs agree after projection to
the order at which the diagrams are equivalent. Thus lower-order equivalence
matches the local labels needed to form a central difference, without matching
individual wall indices or assuming either diagram consistent.

The proof uses `DirectedDiagram.eventually_exists_levelPathProduct_eq_combinedLabel`
to realize both labels on the same short segment, and
`DirectedDiagram.truncation_levelPathProduct` to compare their projections.
Repeated and overlapping indexed walls retain their combined contribution.

Conversely, agreement of these combined labels at every common regular transverse
germ determines all common path products. Thus the combined labels characterize
finite-order equivalence even when two presentations have different crossing sets.
This uses `WallComplement.segmentPathProduct_eq_of_crossingEventProduct_eq` and
`Quiver.Path.wallPathProduct_eq_of_segmentPathProduct_eq` to assemble local data.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  {D : DirectedDiagram (d := d) h H ι} {E : DirectedDiagram (d := d) h H κ}

/-- Equivalence at order `k` matches the projections of combined labels formed at
any higher cutoffs. Regularity and transversality are required only for the two
higher-order wall families, whose indexed presentations may be unrelated. -/
theorem LevelEquivalent.truncation_combinedLabel_eq {k l m : ℕ}
    (hDE : D.LevelEquivalent E k) (hkl : k ≤ l) (hkm : k ≤ m) (θ v : V)
    (hD : θ ∉ singularSupport (fun j : D.active l => (D.wall j).support))
    (hE : θ ∉ singularSupport (fun j : E.active m => (E.wall j).support))
    (hvD : ∀ j : D.active l, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0)
    (hvE : ∀ j : E.active m, θ ∈ (E.wall j).support →
      h.realCharacter (E.wall j).normal v ≠ 0) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.combinedLabel l θ v hD) =
      (d.truncationMap ℒ hkm).bchGroupMap (E.combinedLabel m θ v hE) := by
  obtain ⟨a, haD, haE⟩ := ((D.eventually_exists_levelPathProduct_eq_combinedLabel
    l θ v hD hvD).and (E.eventually_exists_levelPathProduct_eq_combinedLabel
      m θ v hE hvE)).exists
  obtain ⟨x, y, e, hx, hy, he⟩ := haD
  obtain ⟨x', y', e', hx', hy', he'⟩ := haE
  let rD := restrictPrefunctor (fun j : D.active l => (D.wall j).support)
    (Set.inclusion (D.active_mono hkl))
  let rE := restrictPrefunctor (fun j : E.active m => (E.wall j).support)
    (Set.inclusion (E.active_mono hkm))
  have hv : (rD.mapPath e.toPath).vertices.map WallComplement.val =
      (rE.mapPath e'.toPath).vertices.map WallComplement.val := by
    rw [vertices_restrictPrefunctor, vertices_restrictPrefunctor]
    simp only [Quiver.Path.vertices_toPath, List.map_cons, List.map_nil, hx, hy, hx', hy']
  have heq := (levelEquivalent_def D E k).mp hDE
    (rD.mapPath e.toPath) (rE.mapPath e'.toPath) hv
  rw [← D.truncation_levelPathProduct hkl, ← E.truncation_levelPathProduct hkm,
    he, he'] at heq
  exact heq

/-- Equivalent finite-order diagrams have equal combined labels at a common
regular wall germ, with the same transverse crossing direction. -/
theorem LevelEquivalent.combinedLabel_eq {k : ℕ} (hDE : D.LevelEquivalent E k) (θ v : V)
    (hD : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hE : θ ∉ singularSupport (fun j : E.active k => (E.wall j).support))
    (hvD : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0)
    (hvE : ∀ j : E.active k, θ ∈ (E.wall j).support →
      h.realCharacter (E.wall j).normal v ≠ 0) :
    D.combinedLabel k θ v hD = E.combinedLabel k θ v hE := by
  simpa using hDE.truncation_combinedLabel_eq le_rfl le_rfl θ v hD hE hvD hvE

variable (D E) in
/-- Directed diagrams agree at order `k` exactly when their combined labels
agree at every common regular point and every common transverse direction.
Individual wall indices, supports and crossing-time sets need not match. -/
theorem levelEquivalent_iff_combinedLabel_eq (k : ℕ) :
    D.LevelEquivalent E k ↔
      ∀ (θ v : V)
        (hD : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
        (hE : θ ∉ singularSupport (fun j : E.active k => (E.wall j).support)),
        (∀ j : D.active k, θ ∈ (D.wall j).support →
          h.realCharacter (D.wall j).normal v ≠ 0) →
        (∀ j : E.active k, θ ∈ (E.wall j).support →
          h.realCharacter (E.wall j).normal v ≠ 0) →
        D.combinedLabel k θ v hD = E.combinedLabel k θ v hE := by
  constructor
  · exact fun hDE => hDE.combinedLabel_eq
  · intro hlabel
    apply (D.levelEquivalent_def E k).mpr
    intro x y x' y' p q hpq
    rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k),
      E.levelPathProduct_eq_wallPathProduct k q (E.activeLabels_commute k)]
    refine Quiver.Path.wallPathProduct_eq_of_segmentPathProduct_eq _ _
      (D.activeLabels_commute k) _ _ (E.activeLabels_commute k) ?_ p q hpq
    intro u v u' v' e e' hu hv
    apply segmentPathProduct_eq_of_crossingEventProduct_eq
    intro t ht
    rw [D.crossingEventProduct_eq_combinedLabel k e ht,
      E.crossingEventProduct_eq_combinedLabel k e' ht]
    have hregE : AffineMap.lineMap u.val v.val t ∉
        singularSupport (fun j : E.active k => (E.wall j).support) := by
      simpa only [hu, hv] using e'.down.regular t ht
    have hnormalD : ∀ j : D.active k, AffineMap.lineMap u.val v.val t ∈ (D.wall j).support →
        h.realCharacter (D.wall j).normal (v.val - u.val) ≠ 0 := by
      intro j hj
      simpa only [(D.wall j).direction_support, LinearMap.mem_ker] using
        e.down.transverse j ⟨t, ht, hj⟩
    have hnormalE : ∀ j : E.active k, AffineMap.lineMap u.val v.val t ∈ (E.wall j).support →
        h.realCharacter (E.wall j).normal (v.val - u.val) ≠ 0 := by
      intro j hj
      have hj' : AffineMap.lineMap u'.val v'.val t ∈ (E.wall j).support := by
        simpa only [hu, hv] using hj
      simpa only [hu, hv, (E.wall j).direction_support, LinearMap.mem_ker] using
        e'.down.transverse j ⟨t, ht, hj'⟩
    have heq := hlabel _ _ (e.down.regular t ht) hregE hnormalD hnormalE
    simp only [hu, hv] at heq
    -- Event products use the categorical tower carrier; the criterion uses its BCH presentation.
    convert heq using 1
    simp only [hu, hv]
    rfl

end Mei.DirectedDiagram
