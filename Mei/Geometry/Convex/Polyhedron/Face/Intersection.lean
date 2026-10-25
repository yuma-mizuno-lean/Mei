/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Faces of intersections of polyhedra

Every nonempty convex extreme subset of the intersection of two convex
polyhedra is the intersection of actual nonempty exposed faces of the two
polyhedra. The proof splits the active inequalities of the combined finite
presentation. No finite-dimensionality, boundedness, or salience is assumed.
-/

public section

namespace IsExtreme

section General

variable {R V : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid V] [SMul R V]
  {P Q F G : Set V}

/-- Intersections of extreme subsets are extreme in the intersection of their ambient sets. -/
theorem inter_inter (hF : IsExtreme R P F) (hG : IsExtreme R Q G) :
    IsExtreme R (P ∩ Q) (F ∩ G) := by
  refine ⟨fun x hx => ⟨hF.subset hx.1, hG.subset hx.2⟩, ?_⟩
  intro x hx y hy z hz hxy
  exact ⟨hF.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hxy,
    hG.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 hxy⟩

end General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P Q F : Set V}

/-- A nonempty convex extreme subset of an intersection of polyhedra is the
intersection of nonempty exposed faces of the original polyhedra. -/
theorem exists_inter_isExposed_of_isConvexPolyhedron (hF : IsExtreme ℝ (P ∩ Q) F)
    (hP : TauCeti.IsConvexPolyhedron P) (hQ : TauCeti.IsConvexPolyhedron Q)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ F₁ F₂ : Set V, IsExposed ℝ P F₁ ∧ IsExposed ℝ Q F₂ ∧
      F₁.Nonempty ∧ F₂.Nonempty ∧ F = F₁ ∩ F₂ := by
  classical
  obtain ⟨m, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  obtain ⟨n, h, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hQ
  have hbase : {x : V | ∀ i, g i x ≤ 0} ∩ {x : V | ∀ j, h j x ≤ 0} =
      {x : V | ∀ k : Fin m ⊕ Fin n, Sum.elim g h k x ≤ 0} := by
    ext x
    simp [Sum.forall]
  rw [hbase] at hF
  obtain ⟨I, hI⟩ := hF.eq_setOf_active (fun k => (Sum.elim g h k).toAffineMap) hconv hne
  let L := Finset.univ.filter (fun i : Fin m => Sum.inl i ∈ I)
  let R := Finset.univ.filter (fun j : Fin n => Sum.inr j ∈ I)
  let F₁ : Set V := {x | (∀ i, g i x ≤ 0) ∧ ∀ i ∈ L, g i x = 0}
  let F₂ : Set V := {x | (∀ j, h j x ≤ 0) ∧ ∀ j ∈ R, h j x = 0}
  have hsplit : F = F₁ ∩ F₂ := by
    ext x
    rw [hI]
    constructor
    · rintro ⟨hx, hxI⟩
      exact ⟨⟨fun i => hx (Sum.inl i), fun i hi => hxI (Sum.inl i) (Finset.mem_filter.mp hi).2⟩,
        ⟨fun j => hx (Sum.inr j), fun j hj => hxI (Sum.inr j) (Finset.mem_filter.mp hj).2⟩⟩
    · rintro ⟨⟨hx, hxL⟩, ⟨hy, hyR⟩⟩
      constructor
      · intro k
        cases k with
        | inl i => exact hx i
        | inr j => exact hy j
      · intro k hk
        cases k with
        | inl i => exact hxL i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
        | inr j => exact hyR j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  obtain ⟨p, hp⟩ := hne
  have hp₁ : p ∈ F₁ := (hsplit ▸ hp).1
  have hp₂ : p ∈ F₂ := (hsplit ▸ hp).2
  exact ⟨F₁, F₂, Mei.Convex.isExposed_setOf_active g L,
    Mei.Convex.isExposed_setOf_active h R, ⟨p, hp₁⟩, ⟨p, hp₂⟩, hsplit⟩

end IsExtreme

namespace IsExposed

section General

variable {R V : Type*} [TopologicalSpace R] [Ring R] [PartialOrder R] [IsOrderedRing R]
  [ContinuousAdd R] [AddCommMonoid V] [TopologicalSpace V] [Module R V] {P Q F G : Set V}

/-- Intersections of exposed subsets are exposed in the intersection of their
ambient sets. This includes empty intersections and requires no convexity. -/
theorem inter_inter (hF : IsExposed R P F) (hG : IsExposed R Q G) :
    IsExposed R (P ∩ Q) (F ∩ G) := by
  rintro ⟨p, hpF, hpG⟩
  obtain ⟨l, hl⟩ := hF ⟨p, hpF⟩
  obtain ⟨m, hm⟩ := hG ⟨p, hpG⟩
  have hpL := hl ▸ hpF
  have hpM := hm ▸ hpG
  refine ⟨l + m, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxF, hxG⟩
    have hxL := hl ▸ hxF
    have hxM := hm ▸ hxG
    exact ⟨⟨hxL.1, hxM.1⟩, fun y hy => add_le_add (hxL.2 y hy.1) (hxM.2 y hy.2)⟩
  · rintro x ⟨⟨hxP, hxQ⟩, hxmax⟩
    have hsum := hxmax p ⟨hpL.1, hpM.1⟩
    constructor
    · rw [hl]
      refine ⟨hxP, fun y hy => ?_⟩
      exact (add_le_add_iff_right (m x)).mp
        ((add_le_add (hpL.2 y hy) (hpM.2 x hxQ)).trans hsum)
    · rw [hm]
      refine ⟨hxQ, fun y hy => ?_⟩
      exact (add_le_add_iff_left (l x)).mp
        ((add_le_add (hpL.2 x hxP) (hpM.2 y hy)).trans hsum)

end General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P Q F G : Set V}

/-- Every nonempty exposed face of an intersection of polyhedra splits into
nonempty exposed faces of the two original polyhedra. -/
theorem exists_inter_of_isConvexPolyhedron (hF : IsExposed ℝ (P ∩ Q) F)
    (hP : TauCeti.IsConvexPolyhedron P) (hQ : TauCeti.IsConvexPolyhedron Q)
    (hne : F.Nonempty) :
    ∃ F₁ F₂ : Set V, IsExposed ℝ P F₁ ∧ IsExposed ℝ Q F₂ ∧
      F₁.Nonempty ∧ F₂.Nonempty ∧ F = F₁ ∩ F₂ :=
  hF.isExtreme.exists_inter_isExposed_of_isConvexPolyhedron hP hQ
    (hF.convex (hP.convex.inter hQ.convex)) hne

/-- Exposed faces of a polyhedron are closed under taking exposed subfaces.
The polyhedral hypothesis supplies transitivity, which fails for arbitrary convex sets. -/
theorem trans_of_isConvexPolyhedron (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G)
    (hP : TauCeti.IsConvexPolyhedron P) : IsExposed ℝ P G :=
  (hF.isExtreme.trans hG.isExtreme).isExposed_of_isConvexPolyhedron hP
    (hG.convex (hF.convex hP.convex))

end IsExposed
