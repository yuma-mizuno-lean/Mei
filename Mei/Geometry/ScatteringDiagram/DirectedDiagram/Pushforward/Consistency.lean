/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Equivalence.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency

/-!
# Consistency and equivalence under pushforward

Pushing directed diagrams forward along a degree-changing graded Lie map with a
compatible spatial affine equivalence preserves finite-order consistency and
equivalence, with cutoffs related by the cutoff modulus: the property at a source
cutoff covering the modulus of a target order `k` gives the property at `k`. Hence it
preserves consistency and equivalence at all orders. Finite and completed endpoint
transports are natural under pushforward. Labels may die under the map, so the walls
active at a target order may be fewer than the source walls active at the larger cutoff.
The setting is Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Example 2.1(i).
-/

public section

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' ι κ : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (D : DirectedDiagram (d := d) h H ι) (F : DirectedDiagram (d := d) h H κ)
  (P : DirectedWall.Pushforward d d' h h' H H')

/-- Pull back a path avoiding the pushed supports of the walls active at a source cutoff
to a path admissible at that cutoff. -/
private def levelPathPreimage (a : ℕ) :
    WallComplement (fun j : D.active a => ((D.pushforward P).wall j).support) ⥤q
      WallComplement (fun j : D.active a => (D.wall j).support) :=
  P.spatialMap.symm.wallComplementMap (Equiv.refl _)
    (fun j => by rw [Equiv.refl_apply, pushforward_wall_support, P.spatialMap.symm_image_image])

/-- The pulled-back path visits the inverse spatial images of the vertices. -/
private theorem levelPathPreimage_obj_val (a : ℕ)
    (x : WallComplement (fun j : D.active a => ((D.pushforward P).wall j).support)) :
    ((D.levelPathPreimage P a).obj x).val = P.spatialMap.symm x.val :=
  ContinuousAffineEquiv.wallComplementMap_obj_val _ _ _ x

/-- The vertices of a pulled-back path are the inverse spatial images. -/
private theorem vertices_levelPathPreimage (a : ℕ)
    {x y : WallComplement (fun j : D.active a => ((D.pushforward P).wall j).support)}
    (r : AdmissiblePLPath x y) :
    ((D.levelPathPreimage P a).mapPath r).vertices.map WallComplement.val =
      (r.vertices.map WallComplement.val).map P.spatialMap.symm := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    levelPathPreimage_obj_val]

/-- A path avoiding the pushed supports of all walls active at a source cutoff `a`
computes at a target order `k` covered by `a` the image of the source product of its
pullback. -/
private theorem levelPathProduct_restrict_eq (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => ((D.pushforward P).wall j).support)}
    (r : AdmissiblePLPath x y) :
    (D.pushforward P).levelPathProduct k
        ((WallComplement.restrictPrefunctor _
          (Set.inclusion (D.active_pushforward_subset P k ha))).mapPath r) =
      (P.lieHom.truncatedMap k ha).bchGroupMap
        (D.levelPathProduct a ((D.levelPathPreimage P a).mapPath r)) := by
  rw [← D.levelPathProduct_pushforward P k ha]
  apply levelPathProduct_eq_of_vertices_eq
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    WallComplement.restrictPrefunctor_obj_val, levelPathPushforward_obj_val,
    levelPathPreimage_obj_val, ContinuousAffineEquiv.apply_symm_apply]

variable {D F P}

/-- Consistency at a source cutoff covering the modulus of a target order gives
consistency of the pushed diagram at that order. -/
theorem LevelConsistent.pushforward {k a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a) : (D.pushforward P).LevelConsistent k := by
  apply ((D.pushforward P).levelConsistent_iff_loops k).mpr
  intro x p
  obtain ⟨b, q, hq⟩ := (D.pushforward P).exists_loop_levelPathProduct_eq_of_vertices_eq k
    (fun j : D.active a => ((D.pushforward P).wall j).support)
    (fun j => ((D.pushforward P).wall j).isConvexPolyhedron)
    (fun j => ((D.pushforward P).wall j).finrank_direction_add_one) p
  let r := (WallComplement.restrictPrefunctor _
    (Set.inclusion (D.active_pushforward_subset P k ha))).mapPath q
  calc
    (D.pushforward P).levelPathProduct k p =
        (D.pushforward P).levelPathProduct k r :=
      (hq r (WallComplement.vertices_restrictPrefunctor _
        (Set.inclusion (D.active_pushforward_subset P k ha)) q)).symm
    _ = 1 := by
      rw [D.levelPathProduct_restrict_eq P k ha,
        (D.levelConsistent_iff_loops a).mp hD]
      exact map_one _

/-- Pushforward preserves consistency at every order. -/
theorem Consistent.pushforward (hD : D.Consistent) : (D.pushforward P).Consistent :=
  (consistent_iff _).mpr fun k =>
    ((consistent_iff D).mp hD (P.degreeMap.modulus k)).pushforward le_rfl

/-- Equivalence at a source cutoff covering the modulus of a target order gives
equivalence of the pushed diagrams at that order. -/
theorem LevelEquivalent.pushforward {k a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (hDF : D.LevelEquivalent F a) :
    (D.pushforward P).LevelEquivalent (F.pushforward P) k := by
  refine (levelEquivalent_def _ _ k).mpr fun x y x' y' p q hpq => ?_
  -- The pushed supports of all walls of both diagrams active at the source cutoff.
  let W : Unit → D.active a ⊕ F.active a → Set V' := fun _ =>
    Sum.elim (fun j => ((D.pushforward P).wall j).support)
      (fun j => ((F.pushforward P).wall j).support)
  have hpoly : ∀ j c, TauCeti.IsConvexPolyhedron (W j c) := by
    rintro _ (c | c)
    · exact ((D.pushforward P).wall c).isConvexPolyhedron
    · exact ((F.pushforward P).wall c).isConvexPolyhedron
  have hdim : ∀ j c, Module.finrank ℝ (affineSpan ℝ (W j c)).direction + 1 =
      Module.finrank ℝ V' := by
    rintro _ (c | c)
    · exact ((D.pushforward P).wall c).finrank_direction_add_one
    · exact ((F.pushforward P).wall c).finrank_direction_add_one
  obtain ⟨b, c, r, hP, hQ⟩ := (D.pushforward P).exists_common_levelPathProduct_eq
    (F.pushforward P) k k hpoly hdim p q hpq
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  let r₁ := (WallComplement.restrictPrefunctor (W ()) Sum.inl).mapPath r₀
  let r₂ := (WallComplement.restrictPrefunctor (W ()) Sum.inr).mapPath r₀
  have hv₁ : r₁.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection () r)
  have hv₂ : r₂.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection () r)
  have hP' := hP _ ((WallComplement.vertices_restrictPrefunctor _
    (Set.inclusion (D.active_pushforward_subset P k ha)) r₁).trans hv₁)
  have hQ' := hQ _ ((WallComplement.vertices_restrictPrefunctor _
    (Set.inclusion (F.active_pushforward_subset P k ha)) r₂).trans hv₂)
  -- The pulled-back paths share their vertices, so the source equivalence applies.
  have hDF' : D.levelPathProduct a ((D.levelPathPreimage P a).mapPath r₁) =
      F.levelPathProduct a ((F.levelPathPreimage P a).mapPath r₂) := by
    apply (levelEquivalent_def D F a).mp hDF
    refine (D.vertices_levelPathPreimage P a r₁).trans
      (Eq.trans ?_ (F.vertices_levelPathPreimage P a r₂).symm)
    exact congrArg (List.map _) (hv₁.trans hv₂.symm)
  calc
    (D.pushforward P).levelPathProduct k p = _ := hP'.symm
    _ = _ := D.levelPathProduct_restrict_eq P k ha r₁
    _ = _ := congrArg _ hDF'
    _ = _ := (F.levelPathProduct_restrict_eq P k ha r₂).symm
    _ = (F.pushforward P).levelPathProduct k q := hQ'

/-- Pushforward preserves equivalence of directed diagrams. -/
theorem Equivalent.pushforward (hDF : D.Equivalent F) :
    (D.pushforward P).Equivalent (F.pushforward P) :=
  (equivalent_iff _ _).mpr fun k =>
    ((equivalent_iff D F).mp hDF (P.degreeMap.modulus k)).pushforward le_rfl

variable (D P) in
/-- Finite endpoint transport is natural at any source cutoff covering the modulus. -/
@[simp]
theorem levelTransport_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a)
    (x y : WallComplement (fun j : D.active a => (D.wall j).support)) :
    (D.pushforward P).levelTransport k (hD.pushforward ha)
        ((D.levelPathPushforward P k ha).obj x) ((D.levelPathPushforward P k ha).obj y) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (D.levelTransport a hD x y) := by
  obtain ⟨p⟩ := D.exists_level_path a x y
  rw [(D.pushforward P).levelTransport_eq_levelPathProduct _
      ((D.levelPathPushforward P k ha).mapPath p),
    D.levelPathProduct_pushforward, D.levelTransport_eq_levelPathProduct hD p]

variable (P) in
/-- Completed endpoint transport commutes with pushforward. -/
@[simp]
theorem transport_pushforward (hD : D.Consistent) (x y : D.Point) :
    (D.pushforward P).transport hD.pushforward
        ((D.pathPushforward P).obj x) ((D.pathPushforward P).obj y) =
      P.lieHom.completedMap (D.transport hD x y) := by
  obtain ⟨p⟩ := D.exists_path x y
  rw [(D.pushforward P).transport_eq_pathProduct _ ((D.pathPushforward P).mapPath p),
    D.pathProduct_pushforward, D.transport_eq_pathProduct hD p]

end Mei.DirectedDiagram
