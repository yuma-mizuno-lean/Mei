/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.AffineTransport
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness

/-!
# Consistency and outgoing completions under coordinate changes

Compatible spatial and algebraic coordinate changes preserve finite-order consistency
and finite-order equivalence of directed diagrams, with the cutoffs related by the
coordinate change's modulus: consistency or equivalence at a source cutoff covering the
modulus of a target order `k` gives the same property at `k`. In particular they
preserve and reflect consistency and equivalence at all orders. Since incomingness
and outgoingness are also preserved, the image of an outgoing completion of an initial
family is an outgoing completion of the transported initial family. By uniqueness, every
outgoing completion of the transported family is equivalent to that image: forming the
consistent outgoing completion commutes with coordinate changes.

A path at the target order only avoids the walls active there, which may be fewer than
the source walls active at the larger cutoff. It is therefore first moved into general
position for all transported source walls, without changing its product. The pulled-back
path is then admissible at the source cutoff, and `DirectedDiagram.levelPathProduct_image`
compares the two products. The perturbation follows the proofs of
`DirectedDiagram.LevelEquivalent.consistent` and `DirectedDiagram.LevelEquivalent.trans`.

The completions are those of Travis Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5),
Theorem 2.6; here we record their naturality under integral-affine and algebraic coordinate
changes. Translations, changes of the positive degree function, repeated indexed walls and
walls with zero spatial velocity are allowed.
-/

public section

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
  (e : Toric.IntegralAffineEquiv h h')
  (E : DirectedWallSpaces.CoordinateChange (d := d) (e := d') H H')
  (hE : E.tangentEquiv = e.latticeEquiv)

/-- Pull back a path avoiding the transported supports of the walls active at a source
cutoff to a path admissible at that cutoff. -/
private def levelPathPreimage (a : ℕ) :
    WallComplement (fun j : D.active a => ((D.image e E hE).wall j).support) ⥤q
      WallComplement (fun j : D.active a => (D.wall j).support) :=
  e.toContinuousAffineEquiv.symm.wallComplementMap (Equiv.refl _) (by
    intro j
    have he : (e.toAffineEquiv : V → V') = e.toContinuousAffineEquiv :=
      funext fun v => (e.toContinuousAffineEquiv_apply v).symm
    rw [Equiv.refl_apply, image_wall, DirectedWall.image_support, he]
    exact (e.toContinuousAffineEquiv.symm_image_image _).symm)

private theorem levelPathPreimage_obj_val (a : ℕ)
    (x : WallComplement (fun j : D.active a => ((D.image e E hE).wall j).support)) :
    ((D.levelPathPreimage e E hE a).obj x).val = e.toContinuousAffineEquiv.symm x.val :=
  ContinuousAffineEquiv.wallComplementMap_obj_val _ _ _ x

private theorem vertices_levelPathPreimage (a : ℕ)
    {x y : WallComplement (fun j : D.active a => ((D.image e E hE).wall j).support)}
    (r : AdmissiblePLPath x y) :
    ((D.levelPathPreimage e E hE a).mapPath r).vertices.map WallComplement.val =
      (r.vertices.map WallComplement.val).map e.toContinuousAffineEquiv.symm := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    levelPathPreimage_obj_val]

/-- A path avoiding the transported supports of all walls active at a source cutoff `a`
computes at a target order `k` covered by `a` the image of the source product of its
pullback. -/
private theorem levelPathProduct_restrict_eq (k : ℕ) {a : ℕ}
    (ha : E.degreeMap.modulus k ≤ a)
    {x y : WallComplement (fun j : D.active a => ((D.image e E hE).wall j).support)}
    (r : AdmissiblePLPath x y) :
    (D.image e E hE).levelPathProduct k
        ((WallComplement.restrictPrefunctor _
          (Set.inclusion (D.active_image_subset e E hE k ha))).mapPath r) =
      (E.gradedLieHom.truncatedMap k ha).bchGroupMap
        (D.levelPathProduct a ((D.levelPathPreimage e E hE a).mapPath r)) := by
  rw [← D.levelPathProduct_image e E hE k ha]
  apply levelPathProduct_eq_of_vertices_eq
  have happly (v : V') : e (e.toContinuousAffineEquiv.symm v) = v := by
    rw [← Toric.IntegralAffineEquiv.toContinuousAffineEquiv_apply,
      ContinuousAffineEquiv.apply_symm_apply]
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    WallComplement.restrictPrefunctor_obj_val, levelPathImage_obj_val,
    levelPathPreimage_obj_val, happly]

variable {D F e E hE}

/-- Consistency at a source cutoff covering the modulus of a target order gives
consistency of the transported diagram at that order. -/
theorem LevelConsistent.image {k a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a) : (D.image e E hE).LevelConsistent k := by
  let := h'.finiteDimensional
  apply ((D.image e E hE).levelConsistent_iff_loops k).mpr
  intro x p
  cases p with
  | nil => simp
  | @cons y _ p s =>
    let loop := p.cons s
    obtain ⟨ε, hε, hp⟩ :=
      (D.image e E hE).exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k loop
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp p.vertices_head?
    have hv : loop.vertices.map WallComplement.val =
        x.val :: (l.map WallComplement.val ++ [x.val]) := by
      simp only [loop, Quiver.Path.vertices_cons, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil, hl, List.cons_append]
    -- Move the loop into general position for every transported source wall.
    obtain ⟨b, q, hq⟩ := AdmissiblePLPath.exists_loop_forall₂_dist_lt
      (W := fun j : D.active a => ((D.image e E hE).wall j).support)
      (fun j => ((D.image e E hE).wall j).isConvexPolyhedron)
      (fun j => ((D.image e E hE).wall j).finrank_direction_add_one) x.val
      (l := l.map WallComplement.val) hε
    calc
      (D.image e E hE).levelPathProduct k loop =
          (D.image e E hE).levelPathProduct k
            ((WallComplement.restrictPrefunctor _
              (Set.inclusion (D.active_image_subset e E hE k ha))).mapPath q) := by
        refine (hp _ ?_).symm
        rw [hv]
        simpa only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
          WallComplement.restrictPrefunctor_obj_val] using hq
      _ = 1 := by
        rw [D.levelPathProduct_restrict_eq e E hE k ha,
          (D.levelConsistent_iff_loops a).mp hD]
        exact map_one _

/-- Coordinate changes preserve consistency at every order. -/
theorem Consistent.image (hD : D.Consistent) : (D.image e E hE).Consistent :=
  (consistent_iff _).mpr fun k =>
    ((consistent_iff D).mp hD (E.degreeMap.modulus k)).image le_rfl

variable (e E hE) in
/-- Coordinate changes preserve and reflect consistency. -/
@[simp]
theorem consistent_image_iff : (D.image e E hE).Consistent ↔ D.Consistent := by
  refine ⟨fun hD => ?_, Consistent.image⟩
  simpa using hD.image (e := e.symm) (E := E.symm) (hE := by simp [hE])

/-- Equivalence at a source cutoff covering the modulus of a target order gives
equivalence of the transported diagrams at that order. -/
theorem LevelEquivalent.image {k a : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    (hDF : D.LevelEquivalent F a) :
    (D.image e E hE).LevelEquivalent (F.image e E hE) k := by
  refine (levelEquivalent_def _ _ k).mpr fun x y x' y' p q hpq => ?_
  let := h'.finiteDimensional
  -- Stationary padding gives free interior vertices without changing either product.
  obtain ⟨p', hvp, hprodP⟩ := exists_vertices_eq_cons_levelPathProduct_eq (D.image e E hE) k p
  obtain ⟨q', hvq, hprodQ⟩ := exists_vertices_eq_cons_levelPathProduct_eq (F.image e E hE) k q
  have hx : x.val = x'.val := by
    have he := congrArg List.head? hpq
    simpa using he
  have hvpq : p'.vertices.map WallComplement.val = q'.vertices.map WallComplement.val := by
    rw [hvp, hvq, hx, hpq]
  obtain ⟨ε₁, hε₁, hp⟩ :=
    (D.image e E hE).exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k p'
  obtain ⟨ε₂, hε₂, hq⟩ :=
    (F.image e E hE).exists_pos_levelPathProduct_eq_of_forall₂_dist_lt k q'
  -- The transported supports of all walls of both diagrams active at the source cutoff.
  let W : Unit → D.active a ⊕ F.active a → Set V' := fun _ =>
    Sum.elim (fun j => ((D.image e E hE).wall j).support)
      (fun j => ((F.image e E hE).wall j).support)
  have hpoly : ∀ j c, TauCeti.IsConvexPolyhedron (W j c) := by
    rintro _ (c | c)
    · exact ((D.image e E hE).wall c).isConvexPolyhedron
    · exact ((F.image e E hE).wall c).isConvexPolyhedron
  have hdim : ∀ j c, Module.finrank ℝ (affineSpan ℝ (W j c)).direction + 1 =
      Module.finrank ℝ V' := by
    rintro _ (c | c)
    · exact ((D.image e E hE).wall c).finrank_direction_add_one
    · exact ((F.image e E hE).wall c).finrank_direction_add_one
  have hv : p'.vertices.map WallComplement.val =
      x.val :: ((x.val :: p.vertices.dropLast.map WallComplement.val) ++ [y.val]) := by
    have hend := congrArg (List.map WallComplement.val) p.dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton] at hend
    simp only [hvp, List.cons_append, hend]
  -- Move endpoints as well as interior vertices, within both product-stability radii.
  obtain ⟨b, c, r, hr⟩ := CommonWallComplement.exists_forall₂_dist_lt_free_endpoints
    hpoly hdim x.val y.val (l := x.val :: p.vertices.dropLast.map WallComplement.val)
    (List.cons_ne_nil _ _) (lt_min hε₁ hε₂)
  let r₀ := (CommonWallComplement.projectionPrefunctor ()).mapPath r
  let r₁ := (WallComplement.restrictPrefunctor (W ()) Sum.inl).mapPath r₀
  let r₂ := (WallComplement.restrictPrefunctor (W ()) Sum.inr).mapPath r₀
  have hv₁ : r₁.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection () r)
  have hv₂ : r₂.vertices.map WallComplement.val = r.vertices.map CommonWallComplement.val :=
    (WallComplement.vertices_restrictPrefunctor _ _ _).trans
      (CommonWallComplement.vertices_projection () r)
  have hP : (D.image e E hE).levelPathProduct k
      ((WallComplement.restrictPrefunctor _
        (Set.inclusion (D.active_image_subset e E hE k ha))).mapPath r₁) =
        (D.image e E hE).levelPathProduct k p' := by
    apply hp
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_left ε₁ ε₂)
    rw [← hv, ← hv₁, ← WallComplement.vertices_restrictPrefunctor _
      (Set.inclusion (D.active_image_subset e E hE k ha)) r₁] at hnear
    exact hnear
  have hQ : (F.image e E hE).levelPathProduct k
      ((WallComplement.restrictPrefunctor _
        (Set.inclusion (F.active_image_subset e E hE k ha))).mapPath r₂) =
        (F.image e E hE).levelPathProduct k q' := by
    apply hq
    have hnear := hr.imp fun _ _ hab => hab.trans_le (min_le_right ε₁ ε₂)
    rw [← hv, hvpq, ← hv₂, ← WallComplement.vertices_restrictPrefunctor _
      (Set.inclusion (F.active_image_subset e E hE k ha)) r₂] at hnear
    exact hnear
  -- The pulled-back paths share their vertices, so the source equivalence applies.
  have hDF' : D.levelPathProduct a ((D.levelPathPreimage e E hE a).mapPath r₁) =
      F.levelPathProduct a ((F.levelPathPreimage e E hE a).mapPath r₂) := by
    apply (levelEquivalent_def D F a).mp hDF
    refine (D.vertices_levelPathPreimage e E hE a r₁).trans
      (Eq.trans ?_ (F.vertices_levelPathPreimage e E hE a r₂).symm)
    exact congrArg (List.map _) (hv₁.trans hv₂.symm)
  calc
    (D.image e E hE).levelPathProduct k p = _ := hprodP.symm.trans hP.symm
    _ = _ := D.levelPathProduct_restrict_eq e E hE k ha r₁
    _ = _ := congrArg _ hDF'
    _ = _ := (F.levelPathProduct_restrict_eq e E hE k ha r₂).symm
    _ = (F.image e E hE).levelPathProduct k q := hQ.trans hprodQ

/-- Coordinate changes preserve equivalence of directed diagrams. -/
theorem Equivalent.image (hDF : D.Equivalent F) :
    (D.image e E hE).Equivalent (F.image e E hE) :=
  (equivalent_iff _ _).mpr fun k =>
    ((equivalent_iff D F).mp hDF (E.degreeMap.modulus k)).image le_rfl

variable (e E hE) in
/-- Coordinate changes preserve and reflect equivalence of directed diagrams. -/
@[simp]
theorem equivalent_image_iff :
    (D.image e E hE).Equivalent (F.image e E hE) ↔ D.Equivalent F := by
  refine ⟨fun hDF => ?_, Equivalent.image⟩
  simpa using hDF.image (e := e.symm) (E := E.symm) (hE := by simp [hE])

section Completion

variable {ι₀ ι' κ' : Type*} {D₀ : ι₀ → DirectedWall (d := d) h H}

/-- The image of an outgoing completion is an outgoing completion of the transported
initial walls. -/
theorem IsOutgoingCompletion.image {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hD : IsOutgoingCompletion D₀ D) :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) where
  wall_inl j := by rw [image_wall, hD.wall_inl]
  outgoing_inr j := by
    rw [image_wall, DirectedWall.outgoing_image_iff]
    exact hD.outgoing_inr j
  consistent := hD.consistent.image

variable (e E hE) in
/-- A diagram is an outgoing completion exactly when its image is an outgoing completion
of the transported initial walls. -/
theorem isOutgoingCompletion_image_iff {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} :
    IsOutgoingCompletion (fun j => (D₀ j).image e E hE) (D.image e E hE) ↔
      IsOutgoingCompletion D₀ D := by
  refine ⟨fun hD => ⟨fun j => ?_, fun j => ?_, ?_⟩, IsOutgoingCompletion.image⟩
  · apply (DirectedWall.imageEquiv e E hE).injective
    simpa only [DirectedWall.imageEquiv_apply, image_wall] using hD.wall_inl j
  · simpa only [image_wall, DirectedWall.outgoing_image_iff] using hD.outgoing_inr j
  · exact (consistent_image_iff e E hE).mp hD.consistent

/-- Outgoing completion commutes with coordinate changes: every outgoing completion of
the transported initial walls is equivalent to the image of any outgoing completion of
the original initial walls. -/
theorem IsOutgoingCompletion.equivalent_image {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {D' : DirectedDiagram (d := d') h' H' (ι₀ ⊕ κ')} (hD : IsOutgoingCompletion D₀ D)
    (hD' : IsOutgoingCompletion (fun j => (D₀ j).image e E hE) D') :
    D'.Equivalent (D.image e E hE) :=
  outgoingCompletion_unique hD' hD.image

end Completion

end Mei.DirectedDiagram
