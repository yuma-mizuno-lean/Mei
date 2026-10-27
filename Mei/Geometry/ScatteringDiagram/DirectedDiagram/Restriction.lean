/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Invariance
public import Mei.Geometry.Convex.Polyhedron.Path.Refinement
import Mei.Geometry.Convex.Polyhedron.Path.Restriction
import Mei.Geometry.Convex.Polyhedron.Path.Multiplication

/-!
# Restricting indexed directed diagrams

Restrict a directed diagram to a set of wall indices. At any cutoff where the set
retains every active wall, restriction preserves all common path products and hence
consistency. Walls invisible at that cutoff impose no additional path conditions.
Conversely, a path admissible for all active walls is admissible for the restriction, and
its product there is computed on the original walls with the labels outside the set
replaced by the identity.

The comparison uses `Quiver.Path.wallPathProduct_eq_of_refines` on the active
families, whose indices are in bijection. Consistency then follows from
`DirectedDiagram.LevelEquivalent.consistent_iff`. Adjoining the same disjoint
indexed walls preserves finite-order equivalence by
`WallComplement.segmentPathProduct_mul_congr`.
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

/-- Retain the indexed walls in `s`, with their original supports and labels. -/
def restrict (s : Set ι) : DirectedDiagram (d := d) h H s where
  wall j := D.wall j.val
  finite_active k := (D.finite_active k).preimage Subtype.val_injective.injOn

@[simp]
theorem restrict_wall (s : Set ι) (j : s) : (D.restrict s).wall j = D.wall j.val := (rfl)

/-- An active wall of a restriction, as an active wall of the original diagram. -/
private def activeOfRestrict (s : Set ι) (k : ℕ) (j : (D.restrict s).active k) : D.active k :=
  ⟨j.val.val, (D.mem_active k _).mpr (((D.restrict s).mem_active k j.val).mp j.property)⟩

/-- Forgetting the active walls outside `s` keeps paths admissible for the remaining
active walls, which are exactly the active walls of the restriction. -/
def restrictPathPrefunctor (s : Set ι) (k : ℕ) :
    WallComplement (fun j : D.active k => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.restrict s).active k => ((D.restrict s).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active k => (D.wall j).support)
    (activeOfRestrict D s k)

/-- Forgetting walls leaves every vertex at the same ambient point. -/
@[simp]
theorem restrictPathPrefunctor_obj_val (s : Set ι) (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ((D.restrictPathPrefunctor s k).obj x).val = x.val := (rfl)

/-- Forgetting walls preserves the entire ambient vertex list. -/
theorem vertices_restrictPathPrefunctor (s : Set ι) (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} (p : Quiver.Path x y) :
    ((D.restrictPathPrefunctor s k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    restrictPathPrefunctor_obj_val]

/-- The products of a restriction are the products of the original active walls with the
labels outside `s` replaced by the identity. -/
theorem levelPathProduct_restrictPathPrefunctor (s : Set ι) [DecidablePred (· ∈ s)] (k : ℕ)
    (comm : ∀ a b : D.active k,
      affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
        Commute
          (if a.val ∈ s then CompletedGroup.projection k (D.wall a).label else 1 :
            d.truncatedGroup ℒ k)
          (if b.val ∈ s then CompletedGroup.projection k (D.wall b).label else 1))
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.restrict s).levelPathProduct k ((D.restrictPathPrefunctor s k).mapPath p) =
      p.wallPathProduct (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => (if j.val ∈ s then CompletedGroup.projection k (D.wall j).label else 1 :
          d.truncatedGroup ℒ k)) comm := by
  have hf : Function.Injective (activeOfRestrict D s k) := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun j : D.active k => j.val) hab))
  have hlabel : ∀ j, j ∉ range (activeOfRestrict D s k) →
      (if j.val ∈ s then CompletedGroup.projection k (D.wall j).label else 1 :
        d.truncatedGroup ℒ k) = 1 :=
    fun j hj => ite_eq_right_iff.mpr fun hjs => (hj ⟨⟨⟨j.val, hjs⟩,
      ((D.restrict s).mem_active k _).mpr ((D.mem_active k _).mp j.property)⟩, rfl⟩).elim
  have hl : (fun j : D.active k =>
      (if j.val ∈ s then CompletedGroup.projection k (D.wall j).label else 1 :
        d.truncatedGroup ℒ k)) ∘ activeOfRestrict D s k =
      fun j : (D.restrict s).active k =>
        (CompletedGroup.projection k ((D.restrict s).wall j).label : d.truncatedGroup ℒ k) := by
    funext j
    -- The surviving labels agree; the tower and BCH presentations of the group coincide.
    simp only [Function.comp_apply, activeOfRestrict, j.val.property]
    rfl
  rw [← Quiver.Path.wallPathProduct_restrict _ _ comm _ hf hlabel p,
    levelPathProduct_eq_wallPathProduct _ k _ ((D.restrict s).activeLabels_commute k)]
  simp only [hl]
  rfl

/-- Deleting only walls invisible at order `k` preserves order-`k` equivalence.
No condition is imposed on the deleted walls at higher orders. -/
theorem levelEquivalent_restrict {k : ℕ} {s : Set ι} (hs : D.active k ⊆ s) :
    D.LevelEquivalent (D.restrict s) k := by
  let E := D.restrict s
  let f : E.active k → D.active k := fun j =>
    ⟨j.val.val, by simpa only [mem_active, E, restrict_wall] using j.property⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : D.active k => z.val) hab))
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨⟨⟨a.val, hs a.property⟩, ?_⟩, Subtype.ext rfl⟩
    simpa only [mem_active, E, restrict_wall] using a.property
  apply (D.levelEquivalent_def E k).mpr
  intro x y x' y' p q hpq
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k),
    E.levelPathProduct_eq_wallPathProduct k q (E.activeLabels_commute k)]
  symm
  refine Quiver.Path.wallPathProduct_eq_of_refines
    (fun j : D.active k => h.realCharacter (D.wall j).normal) _ (D.activeLabels_commute k)
    (fun j : E.active k => h.realCharacter (E.wall j).normal) _
    (E.activeLabels_commute k) (f := f) (fun _ => subset_rfl)
    (fun a => ?_) (fun a => ?_) (fun _ => rfl) (fun _ => rfl) p q hpq.symm
  · obtain ⟨j, rfl⟩ := hsurj a
    exact fun z hz => mem_iUnion₂.mpr ⟨j, rfl, hz⟩
  · intro a₁ ha₁ a₂ ha₂ hne
    exact (hne (hf (ha₁.trans ha₂.symm))).elim

/-- At a cutoff retaining all active walls, a restriction is consistent exactly
when the original diagram is. -/
theorem levelConsistent_restrict_iff {k : ℕ} {s : Set ι} (hs : D.active k ⊆ s) :
    (D.restrict s).LevelConsistent k ↔ D.LevelConsistent k :=
  (D.levelEquivalent_restrict hs).consistent_iff.symm

variable {F : DirectedDiagram (d := d) h H ι}

private theorem levelPathProduct_restrict_union {s t u : Set ι} {k : ℕ}
    (hst : (F.restrict s).LevelEquivalent (F.restrict t) k)
    (hsu : Disjoint s u) (htu : Disjoint t u)
    {x y : WallComplement (fun j : F.active k => (F.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (F.restrict (s ∪ u)).levelPathProduct k
        ((F.restrictPathPrefunctor (s ∪ u) k).mapPath p) =
      (F.restrict (t ∪ u)).levelPathProduct k
        ((F.restrictPathPrefunctor (t ∪ u) k).mapPath p) := by
  classical
  let := h.finiteDimensional
  let ν := fun j : F.active k => h.realCharacter (F.wall j).normal
  let a := fun (v : Set ι) (j : F.active k) =>
    v.mulIndicator (fun j => CompletedGroup.projection k (F.wall j).label) j.val
  have comm (v w : Set ι) (j j' : F.active k)
      (hjj' : affineSpan ℝ (F.wall j).support = affineSpan ℝ (F.wall j').support) :
      Commute (a v j) (a w j') := by
    by_cases hj : j.val ∈ v <;> by_cases hj' : j'.val ∈ w
    · simpa only [a, Set.mulIndicator_apply, hj, hj', ↓reduceIte] using
        F.activeLabels_commute k j j' hjj'
    · simp only [a, Set.mulIndicator_apply, hj, hj', ↓reduceIte, Commute.one_right]
    · simp only [a, Set.mulIndicator_apply, hj, hj', ↓reduceIte, Commute.one_left]
    · simp only [a, Set.mulIndicator_apply, hj, hj', ↓reduceIte, Commute.one_left]
  have formula (v : Set ι)
      {x y : WallComplement (fun j : F.active k => (F.wall j).support)}
      (p : AdmissiblePLPath x y) :
      (F.restrict v).levelPathProduct k ((F.restrictPathPrefunctor v k).mapPath p) =
        p.wallPathProduct ν (a v) (comm v v) := by
    have he := F.levelPathProduct_restrictPathPrefunctor v k (fun j j' hjj' => by
      -- Identify the categorical tower operations with the BCH operations.
      convert comm v v j j' hjj' using 1 <;> rfl) p
    -- The formula uses the concrete BCH group and the labels use its tower presentation.
    convert he using 1
    rfl
  have prod_union (v : Set ι) (hvu : Disjoint v u) :
      a (v ∪ u) = fun j => a v j * a u j := by
    funext j
    exact congrFun (Set.mulIndicator_union_of_disjoint hvu
      (fun j => CompletedGroup.projection k (F.wall j).label)) j.val
  -- Compare the original labels on every common segment.
  rw [formula, formula]
  have hab {x y : WallComplement (fun j : F.active k => (F.wall j).support)}
      (e : x ⟶ y) :
      segmentPathProduct ν (a s) (comm s s) e =
        segmentPathProduct ν (a t) (comm t t) e := by
    have he := (levelEquivalent_def _ _ k).mp hst
      ((F.restrictPathPrefunctor s k).mapPath e.toPath)
      ((F.restrictPathPrefunctor t k).mapPath e.toPath)
      ((F.vertices_restrictPathPrefunctor s k e.toPath).trans
        (F.vertices_restrictPathPrefunctor t k e.toPath).symm)
    rw [formula, formula, Quiver.Path.wallPathProduct_toPath,
      Quiver.Path.wallPathProduct_toPath] at he
    -- Equality is transported from the concrete BCH carrier to its tower carrier.
    convert he using 1
    rfl
  have hs := prod_union s hsu
  have ht := prod_union t htu
  induction p with
  | nil =>
    simp only [Quiver.Path.wallPathProduct_nil]
    -- Both identities are the identity of the same BCH group.
    rfl
  | cons p e ih =>
    simp only [Quiver.Path.wallPathProduct_cons, ih]
    congr 1
    -- `hs` and `ht` replace indicator functions; commutation witnesses are propositions.
    simpa only [← hs, ← ht] using segmentPathProduct_mul_congr
      (fun j : F.active k => (F.wall j).isConvexPolyhedron.isClosed)
      ν (a s) (a t) (a u) (comm s s) (comm t t) (comm u u) (comm s u) (comm t u) hab e

/-- Adjoining the same indexed walls to equivalent subdiagrams preserves
equivalence at a fixed cutoff. The added indices are disjoint from each original
set, but supports may coincide and labels need not commute globally. -/
theorem LevelEquivalent.restrict_union {s t u : Set ι} {k : ℕ}
    (hst : (F.restrict s).LevelEquivalent (F.restrict t) k)
    (hsu : Disjoint s u) (htu : Disjoint t u) :
    (F.restrict (s ∪ u)).LevelEquivalent (F.restrict (t ∪ u)) k := by
  apply (levelEquivalent_def _ _ k).mpr
  intro x y x' y' p q hpq
  obtain ⟨a, b, r, hp, hq⟩ := (F.restrict (s ∪ u)).exists_common_levelPathProduct_eq
    (F.restrict (t ∪ u)) k k
    (W := fun _ : Unit => fun j : F.active k => (F.wall j).support)
    (fun _ j => (F.wall j).isConvexPolyhedron)
    (fun _ j => (F.wall j).finrank_direction_add_one) p q hpq
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  have hv : r₀.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    CommonWallComplement.vertices_projection () r
  exact (hp _ ((F.vertices_restrictPathPrefunctor (s ∪ u) k r₀).trans hv)).symm.trans
    ((levelPathProduct_restrict_union hst hsu htu r₀).trans
      (hq _ ((F.vertices_restrictPathPrefunctor (t ∪ u) k r₀).trans hv)))

end Mei.DirectedDiagram
