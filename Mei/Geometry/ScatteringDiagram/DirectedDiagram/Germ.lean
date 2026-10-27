/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing

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

variable (D) in
/-- Lowering the cutoff projects a regular combined label to the combined label
of the surviving walls, for every vector `v`. Walls killed by truncation
contribute no factor. -/
theorem truncation_combinedLabel {k l : ℕ} (hkl : k ≤ l) (θ v : V)
    (hl : θ ∉ singularSupport (fun j : D.active l => (D.wall j).support))
    (hk : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.combinedLabel l θ v hl) =
      D.combinedLabel k θ v hk := by
  classical
  -- Filter an enumeration of the incident walls to those surviving at the lower cutoff.
  let S := (Set.toFinite {j : D.active l | θ ∈ (D.wall j).support}).toFinset.toList
  let q : D.active l → Option (D.active k) := fun j =>
    if hj : j.val ∈ D.active k then some ⟨j.val, hj⟩ else none
  have hq (a : D.active l) (b : D.active k) : q a = some b ↔ a.val = b.val := by
    simp only [q]
    split_ifs with ha
    · simp only [Option.some.injEq, Subtype.ext_iff]
    · simp only [false_iff]
      intro hab
      exact ha (hab ▸ b.property)
  have hnodup : (S.filterMap q).Nodup := by
    apply List.Nodup.filterMap ?_ (Finset.nodup_toList _)
    intro a a' b hab ha'b
    exact Subtype.ext ((hq a b).mp hab |>.trans ((hq a' b).mp ha'b).symm)
  have hmem (b : D.active k) : b ∈ S.filterMap q ↔ θ ∈ (D.wall b).support := by
    simp only [List.mem_filterMap, hq]
    constructor
    · rintro ⟨a, ha, hab⟩
      have ha : θ ∈ (D.wall a).support := by simpa [S] using ha
      simpa only [hab] using ha
    · intro hb
      exact ⟨⟨b.val, D.active_mono hkl b.property⟩, by simpa [S] using hb, rfl⟩
  rw [D.combinedLabel_eq_prod l θ v hl S (Finset.nodup_toList _)
    (fun j => by simp [S]), D.combinedLabel_eq_prod k θ v hk _ hnodup hmem]
  -- Work with the tower group instances when mapping the enumerated product.
  let F := ((d.groupTower ℒ).map (CategoryTheory.homOfLE hkl).op).hom
  have hproj (a : D.active l) : F (CompletedGroup.projection l (D.wall a).label) =
      CompletedGroup.projection k (D.wall a).label :=
    CompletedGroup.map_projection k l hkl (D.wall a).label
  have hprod (s : List (D.active l)) :
      F
        ((s.map fun j : D.active l => CompletedGroup.projection l (D.wall j).label ^
          (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)).prod) =
      ((s.filterMap q).map fun j : D.active k => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)).prod := by
    induction s with
    | nil => exact map_one F
    | cons a s ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [map_mul, map_zpow, hproj, ih]
      by_cases ha : a.val ∈ D.active k
      · simp only [List.filterMap_cons, q, dite_eq_left ha, List.map_cons, List.prod_cons]
      · have hone : CompletedGroup.projection k (D.wall a).label = 1 := by
          simpa only [mem_active, not_not] using ha
        simp only [List.filterMap_cons, q, dite_eq_right ha, hone, one_zpow, one_mul]
  -- The tower transition is the BCH truncation map, as in `groupTower_map_hom`.
  exact hprod S

end Mei.DirectedDiagram
