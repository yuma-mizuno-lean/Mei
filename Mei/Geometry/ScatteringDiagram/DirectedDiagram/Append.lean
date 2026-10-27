/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ

/-!
# Adjoining directed wall families

`DirectedDiagram.append` adjoins a correction family to an existing diagram,
retaining the two index types separately even when supports coincide. Both
families may be infinite, provided that they are finitely active at each order.
Restriction to the left indices recovers the original diagram up to reindexing.

If the appended labels vanish at a cutoff, the appended diagram and the original
have equal products on all common paths and the same consistency at that cutoff.
The comparison also holds at every lower cutoff. Thus adjoining corrections of
birth order `k + 1` preserves the transport already constructed through order `k`.
No consistency or commutativity at higher orders is assumed.

More generally, adjoining the same wall family preserves equivalence at any
cutoff, and hence at all orders. At a regular germ of the union the combined
label is the product of the two families' combined labels; this lets an initial
presentation be replaced while retaining a fixed correction family.

The comparison uses `DirectedDiagram.levelEquivalent_restrict` to discard
invisible walls and `DirectedDiagram.Refinement.ofEquiv` to identify the retained
indices. These are the same restriction and reindexing comparisons used in
`DirectedDiagram.outgoingCompletion_unique`. The general congruence uses
`DirectedDiagram.levelEquivalent_iff_combinedLabel_eq` and the enumeration formula
`DirectedDiagram.combinedLabel_eq_prod`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι) (E : DirectedDiagram (d := d) h H κ)

/-- Adjoin two indexed wall families, preserving repeated walls and their labels. -/
def append : DirectedDiagram (d := d) h H (ι ⊕ κ) where
  wall := Sum.elim D.wall E.wall
  finite_active k :=
    Set.finite_preimage_inl_and_inr.mp ⟨D.finite_active k, E.finite_active k⟩

@[simp]
theorem append_wall_inl (j : ι) : (D.append E).wall (.inl j) = D.wall j := (rfl)

@[simp]
theorem append_wall_inr (j : κ) : (D.append E).wall (.inr j) = E.wall j := (rfl)

/-- The active indices of the union are exactly the active indices of its two families. -/
theorem active_append (k : ℕ) :
    (D.append E).active k = Sum.inl '' D.active k ∪ Sum.inr '' E.active k := by
  ext j
  cases j <;> simp [mem_active]

/-- Restricting the appended diagram to its original indices recovers the original
diagram, including all path products, up to the canonical reindexing. -/
theorem restrict_append_left_equivalent :
    ((D.append E).restrict (range (Sum.inl : ι → ι ⊕ κ))).Equivalent D := by
  exact (Refinement.ofEquiv
    (Equiv.ofInjective (Sum.inl : ι → ι ⊕ κ) Sum.inl_injective)
    (fun j => by rw [restrict_wall, Equiv.ofInjective_apply, append_wall_inl])).equivalent

/-- Forget the appended walls while keeping the same geometric path. This is
defined at every cutoff, including those where the new walls are active. -/
def appendLeftPathPrefunctor (k : ℕ) :
    WallComplement (fun j : (D.append E).active k => ((D.append E).wall j).support) ⥤q
      WallComplement (fun j : D.active k => (D.wall j).support) :=
  WallComplement.restrictPrefunctor
    (fun j : (D.append E).active k => ((D.append E).wall j).support)
    (fun j : D.active k => ⟨Sum.inl j.val, by
      simpa only [mem_active, append_wall_inl] using j.property⟩)

@[simp]
theorem appendLeftPathPrefunctor_obj_val (k : ℕ)
    (x : WallComplement
      (fun j : (D.append E).active k => ((D.append E).wall j).support)) :
    ((D.appendLeftPathPrefunctor E k).obj x).val = x.val := (rfl)

/-- Forgetting appended walls preserves the entire ambient vertex list. -/
theorem vertices_appendLeftPathPrefunctor (k : ℕ)
    {x y : WallComplement
      (fun j : (D.append E).active k => ((D.append E).wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((D.appendLeftPathPrefunctor E k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  exact WallComplement.vertices_restrictPrefunctor _
    (fun j : D.active k => ⟨Sum.inl j.val, by
      simpa only [mem_active, append_wall_inl] using j.property⟩) p

/-- Adjoining labels invisible at order `k` preserves every common order-`k`
path product. No condition is imposed at later orders. -/
theorem append_levelEquivalent_left {k : ℕ}
    (hE : ∀ j, CompletedGroup.projection k (E.wall j).label = 1) :
    (D.append E).LevelEquivalent D k := by
  have hs : (D.append E).active k ⊆ range (Sum.inl : ι → ι ⊕ κ) := by
    rintro (j | j) hj
    · exact ⟨j, rfl⟩
    · exact (((D.append E).mem_active k (.inr j)).mp hj (hE j)).elim
  exact ((D.append E).levelEquivalent_restrict hs).trans
    ((equivalent_iff _ _).mp (D.restrict_append_left_equivalent E) k)

/-- The actual path obtained by forgetting invisible appended walls has the
original product. In particular, no new admissible path has to be chosen. -/
theorem levelPathProduct_appendLeftPathPrefunctor {k : ℕ}
    (hE : ∀ j, CompletedGroup.projection k (E.wall j).label = 1)
    {x y : WallComplement
      (fun j : (D.append E).active k => ((D.append E).wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k ((D.appendLeftPathPrefunctor E k).mapPath p) =
      (D.append E).levelPathProduct k p := by
  exact (((D.append E).levelEquivalent_def D k).mp
    (D.append_levelEquivalent_left E hE) p
    ((D.appendLeftPathPrefunctor E k).mapPath p)
    (D.vertices_appendLeftPathPrefunctor E k p).symm).symm

/-- Corrections invisible at order `k` preserve consistency at that order. -/
theorem append_levelConsistent_iff {k : ℕ}
    (hE : ∀ j, CompletedGroup.projection k (E.wall j).label = 1) :
    (D.append E).LevelConsistent k ↔ D.LevelConsistent k :=
  (D.append_levelEquivalent_left E hE).consistent_iff

/-- Corrections invisible at order `k` preserve transport at every earlier order too. -/
theorem append_levelEquivalent_left_of_le {k l : ℕ} (hlk : l ≤ k)
    (hE : ∀ j, CompletedGroup.projection k (E.wall j).label = 1) :
    (D.append E).LevelEquivalent D l := by
  apply D.append_levelEquivalent_left E
  intro j
  have he := CompletedGroup.map_projection l k hlk (E.wall j).label
  rw [hE j, map_one] at he
  exact he.symm

/-- The original family's singular points remain singular after adjoining walls. -/
theorem singularSupport_append_left_subset (k : ℕ) :
    singularSupport (fun j : D.active k => (D.wall j).support) ⊆
      singularSupport (fun j : (D.append E).active k => ((D.append E).wall j).support) := by
  let f : D.active k → (D.append E).active k := fun j =>
    ⟨.inl j.val, by simpa only [mem_active, append_wall_inl] using j.property⟩
  exact singularSupport_comp_subset
    (fun j : (D.append E).active k => ((D.append E).wall j).support) f

/-- The appended family's singular points remain singular in the union. -/
theorem singularSupport_append_right_subset (k : ℕ) :
    singularSupport (fun j : E.active k => (E.wall j).support) ⊆
      singularSupport (fun j : (D.append E).active k => ((D.append E).wall j).support) := by
  let f : E.active k → (D.append E).active k := fun j =>
    ⟨.inr j.val, by simpa only [mem_active, append_wall_inr] using j.property⟩
  exact singularSupport_comp_subset
    (fun j : (D.append E).active k => ((D.append E).wall j).support) f

/-- At a regular germ of the union, adjoining wall families multiplies their
combined labels. No ordering of individual coincident walls is required. -/
@[simp]
theorem combinedLabel_append (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport
      (fun j : (D.append E).active k => ((D.append E).wall j).support)) :
    (D.append E).combinedLabel k θ v hθ =
      D.combinedLabel k θ v (fun hs => hθ (D.singularSupport_append_left_subset E k hs)) *
      E.combinedLabel k θ v (fun hs => hθ (D.singularSupport_append_right_subset E k hs)) := by
  classical
  let f : D.active k → (D.append E).active k := fun j =>
    ⟨.inl j.val, by simpa only [mem_active, append_wall_inl] using j.property⟩
  let g : E.active k → (D.append E).active k := fun j =>
    ⟨.inr j.val, by simpa only [mem_active, append_wall_inr] using j.property⟩
  let S := (Set.toFinite {j : D.active k | θ ∈ (D.wall j).support}).toFinset
  let T := (Set.toFinite {j : E.active k | θ ∈ (E.wall j).support}).toFinset
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (Sum.inl_injective (congrArg Subtype.val hab))
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (Sum.inr_injective (congrArg Subtype.val hab))
  have hdisj : List.Disjoint (S.toList.map f) (T.toList.map g) := by
    apply List.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
    obtain ⟨b, _, he⟩ := List.mem_map.mp hj'
    have he' : Sum.inr b.val = (Sum.inl a.val : ι ⊕ κ) :=
      congrArg (fun z : (D.append E).active k => z.val) he
    cases he'
  have hmem (j : (D.append E).active k) :
      j ∈ S.toList.map f ++ T.toList.map g ↔ θ ∈ ((D.append E).wall j).support := by
    rcases j with ⟨j | j, hj⟩
    · have hjD : j ∈ D.active k := by simpa only [mem_active, append_wall_inl] using hj
      simp [S, T, f, g, Subtype.ext_iff, (D.mem_active k j).mp hjD]
    · have hjE : j ∈ E.active k := by simpa only [mem_active, append_wall_inr] using hj
      simp [S, T, f, g, Subtype.ext_iff, (E.mem_active k j).mp hjE]
  rw [(D.append E).combinedLabel_eq_prod k θ v hθ _
    ((S.nodup_toList.map hf).append (T.nodup_toList.map hg) hdisj) hmem,
    D.combinedLabel_eq_prod k θ v _ S.toList S.nodup_toList (by simp [S]),
    E.combinedLabel_eq_prod k θ v _ T.toList T.nodup_toList (by simp [T])]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def,
    f, g, append_wall_inl, append_wall_inr]
  -- The categorical tower and concrete BCH presentations have the same multiplication.
  rfl

variable {η : Type*} {D E}

/-- Adjoining the same indexed walls preserves finite-order equivalence, including
when the two original presentations have unrelated or cancelling wall germs. -/
theorem LevelEquivalent.append {k : ℕ} (hDE : D.LevelEquivalent E k)
    (F : DirectedDiagram (d := d) h H η) :
    (D.append F).LevelEquivalent (E.append F) k := by
  apply (levelEquivalent_iff_combinedLabel_eq _ _ k).mpr
  intro θ v hD hE hvD hvE
  have hregD := fun hs => hD (D.singularSupport_append_left_subset F k hs)
  have hregE := fun hs => hE (E.singularSupport_append_left_subset F k hs)
  have htransD : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0 := by
    intro j hj
    exact hvD ⟨.inl j.val, by simpa only [mem_active, append_wall_inl] using j.property⟩ hj
  have htransE : ∀ j : E.active k, θ ∈ (E.wall j).support →
      h.realCharacter (E.wall j).normal v ≠ 0 := by
    intro j hj
    exact hvE ⟨.inl j.val, by simpa only [mem_active, append_wall_inl] using j.property⟩ hj
  rw [combinedLabel_append, combinedLabel_append,
    hDE.combinedLabel_eq θ v hregD hregE htransD htransE]

/-- Adjoining the same indexed walls preserves all-order equivalence. -/
theorem Equivalent.append (hDE : D.Equivalent E)
    (F : DirectedDiagram (d := d) h H η) : (D.append F).Equivalent (E.append F) := by
  exact (equivalent_iff _ _).mpr fun k => ((equivalent_iff _ _).mp hDE k).append F

end Mei.DirectedDiagram
