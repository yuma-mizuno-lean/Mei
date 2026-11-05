/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Completed
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic

/-!
# Germ labels under pushforward

Let `P` be `DirectedWall.Pushforward` data, with spatial affine equivalence `A`, and let `D` be a
directed diagram. The singular support of the walls of `D.pushforward P` active at order `k` is
the image under `A` of the singular support of a subfamily of the walls of `D` active at the
cutoff modulus of `k`. Hence regular points and generic points of an affine subspace `B` are
carried to regular points and generic points of the image of `B`
(`DirectedDiagram.IsRegular.pushforward`, `DirectedDiagram.IsGenericPoint.pushforward`).

The normal map of `P` sends each normal to one whose real extension, composed with the linear
part of `A`, is a positive multiple of the original real extension. So crossing signs are kept,
and the combined crossing label of the pushforward at order `k`, the point `A θ` and the
direction `A v` is the truncated image of the combined label of `D` at any source order `a`
covering the cutoff modulus (`DirectedDiagram.combinedLabel_pushforward`). For the proof, the
pushed walls active at order `k` through `A θ` embed into the walls of `D` active at order `a`
through `θ` (`DirectedDiagram.activePushforwardEmbedding`,
`DirectedDiagram.map_incidentActive_pushforward_subset`), and the remaining walls of `D` through
`θ` have trivial pushed labels at order `k`
(`DirectedDiagram.projection_pushforward_wall_label_eq_one`). The germ label of the
pushforward is the image of the germ label under the completed Lie map
(`DirectedDiagram.germLabel_pushforward`). Hence every diagram equivalent to the pushforward has
this germ label at every image of a generic point that is generic for it
(`DirectedDiagram.Equivalent.germLabel_eq_pushforward`).

This is the germ-level form of `DirectedDiagram.pathProduct_pushforward`: no function-wall
grouping of the source or of the target is involved. It compares the wall functions on a ray of
two completions related by a change of lattice, as in Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, Theorem 9.5 (arXiv:2503.03719v1).
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
  (D : DirectedDiagram (d := d) h H ι)
  (P : DirectedWall.Pushforward d d' h h' H H')

/-- The singular support of the pushed walls active at order `k` is the spatial image of the
singular support of the same walls of `D`. -/
theorem singularSupport_pushforward (k : ℕ) :
    singularSupport (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) =
      P.spatialMap ''
        singularSupport (fun j : (D.pushforward P).active k => (D.wall j).support) := by
  simp only [pushforward_wall_support]
  exact singularSupport_image _ _

/-- A point outside the singular support of the walls of `D` active at a source order covering
the cutoff modulus of `k` has image outside the singular support of the pushed walls active at
order `k`. -/
theorem notMem_singularSupport_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    {θ : V} (hθ : θ ∉ singularSupport (fun j : D.active a => (D.wall j).support)) :
    P.spatialMap θ ∉ singularSupport
      (fun j : (D.pushforward P).active k => ((D.pushforward P).wall j).support) := by
  rw [singularSupport_pushforward, P.spatialMap.injective.mem_set_image]
  exact fun hs => hθ (singularSupport_comp_subset _
    (Set.inclusion (D.active_pushforward_subset P k ha)) hs)

variable {D} in
/-- Regular points are carried to regular points of the pushforward. -/
theorem IsRegular.pushforward {θ : V} (hθ : D.IsRegular θ) :
    (D.pushforward P).IsRegular (P.spatialMap θ) :=
  ((D.pushforward P).isRegular_iff _).mpr fun k =>
    D.notMem_singularSupport_pushforward P k le_rfl (hθ.notMem_singularSupport _)

/-- The affine span of a pushed wall is the image of the affine span of the wall. -/
theorem affineSpan_pushforward_wall_support (j : ι) :
    affineSpan ℝ ((D.pushforward P).wall j).support =
      (affineSpan ℝ (D.wall j).support).map P.spatialMap.toAffineEquiv.toAffineMap := by
  rw [AffineSubspace.map_span, pushforward_wall_support, AffineEquiv.coe_toAffineMap,
    ContinuousAffineEquiv.coe_coe]

variable {D} in
/-- Generic points of an affine subspace `B` are carried to generic points of its image. -/
theorem IsGenericPoint.pushforward {B : AffineSubspace ℝ V} {θ : V}
    (hθ : D.IsGenericPoint B θ) :
    (D.pushforward P).IsGenericPoint (B.map P.spatialMap.toAffineEquiv.toAffineMap)
      (P.spatialMap θ) where
  mem := AffineSubspace.mem_map_of_mem _ hθ.mem
  isRegular := hθ.isRegular.pushforward P
  affineSpan_eq {k} j hj := by
    rw [pushforward_wall_support, P.spatialMap.injective.mem_set_image] at hj
    rw [affineSpan_pushforward_wall_support,
      hθ.affineSpan_eq (Set.inclusion (D.active_pushforward_subset P k le_rfl) j) hj]

/-- Pushing forward keeps the crossing sign of every wall: the pushed normal pairs with the image
of a direction as a positive multiple of the original pairing. -/
theorem pos_realCharacter_pushforward_normal_iff (j : ι) (v : V) :
    0 < h'.realCharacter ((D.pushforward P).wall j).normal (P.spatialMap.toAffineEquiv.linear v) ↔
      0 < h.realCharacter (D.wall j).normal v := by
  obtain ⟨r, hr, he⟩ := P.exists_realCharacter_normalMap_apply (D.wall j).normal
  rw [pushforward_wall, DirectedWall.pushforward_normal, he,
    mul_pos_iff_of_pos_left (by exact_mod_cast hr)]

/-- A pushed wall contains the image `A θ` exactly when the original wall contains `θ`. -/
theorem spatialMap_mem_pushforward_wall_support_iff (j : ι) (θ : V) :
    P.spatialMap θ ∈ ((D.pushforward P).wall j).support ↔ θ ∈ (D.wall j).support := by
  rw [pushforward_wall_support, P.spatialMap.injective.mem_set_image]

/-- The walls of the pushforward active at order `k` are among the walls of `D` active at every
source order `a` covering the cutoff modulus of `k`. -/
def activePushforwardEmbedding (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    (D.pushforward P).active k ↪ D.active a :=
  ⟨Set.inclusion (D.active_pushforward_subset P k ha), Set.inclusion_injective _⟩

/-- The embedding of active walls keeps the wall index. -/
@[simp]
theorem coe_activePushforwardEmbedding (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (j : (D.pushforward P).active k) :
    (D.activePushforwardEmbedding P k ha j : ι) = j := by
  simp [activePushforwardEmbedding]

/-- The pushed walls active at order `k` through the image `A θ` embed into the walls of `D`
active at the source order `a` through `θ`, for `a` covering the cutoff modulus of `k`. -/
theorem map_incidentActive_pushforward_subset (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (θ : V) :
    ((D.pushforward P).incidentActive k (P.spatialMap θ)).map
        (D.activePushforwardEmbedding P k ha) ⊆ D.incidentActive a θ := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
  rw [mem_incidentActive, spatialMap_mem_pushforward_wall_support_iff] at hc
  rwa [mem_incidentActive, coe_activePushforwardEmbedding]

/-- A wall of `D` through `θ`, active at the source order `a`, that is not the image of a pushed
wall active at order `k` through `A θ` has trivial pushed label at order `k`. -/
theorem projection_pushforward_wall_label_eq_one (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a) {θ : V} {b : D.active a} (hb : b ∈ D.incidentActive a θ)
    (hnot : b ∉ ((D.pushforward P).incidentActive k (P.spatialMap θ)).map
      (D.activePushforwardEmbedding P k ha)) :
    CompletedGroup.projection k ((D.pushforward P).wall b).label = 1 := by
  have hinactive : b.val ∉ (D.pushforward P).active k := fun hbk => hnot
    (Finset.mem_map.mpr ⟨⟨b.val, hbk⟩, by
      rwa [mem_incidentActive, spatialMap_mem_pushforward_wall_support_iff,
        ← mem_incidentActive], Subtype.ext (coe_activePushforwardEmbedding ..)⟩)
  simpa only [mem_active, not_not] using hinactive

/-- **Combined labels under pushforward.** At target order `k` and any source order `a` covering
the cutoff modulus of `k`, the combined crossing label of the pushforward at the image `A θ` of
a point `θ` outside the singular support of the walls active at order `a`, in the image `A v` of
a direction `v`, is the truncated image of the combined label of `D` at `θ` and `v`. -/
theorem combinedLabel_pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active a => (D.wall j).support)) :
    (D.pushforward P).combinedLabel k (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v)
        (D.notMem_singularSupport_pushforward P k ha hθ) =
      (P.lieHom.truncatedMap k ha).bchGroupMap (D.combinedLabel a θ v hθ) := by
  /- Both combined labels are products over the active walls through the point
  (`combinedLabel_eq_noncommProd_incidentActive`). The truncated BCH map sends each source factor
  to the order-`k` projection of the pushed label with the original crossing sign. These factors
  are trivial off the image of the pushed walls through `A θ`
  (`projection_pushforward_wall_label_eq_one`), so the product reindexes along the embedding
  (`map_incidentActive_pushforward_subset`, `Finset.noncommProd_map` and
  `Finset.noncommProd_subset`). The pushforward keeps every crossing sign
  (`pos_realCharacter_pushforward_normal_iff`). -/
  let e := D.activePushforwardEmbedding P k ha
  -- The truncated BCH map of the pushforward, between the objects of the two group towers.
  let F : (d.groupTower ℒ).obj (Opposite.op a) →* (d'.groupTower ℳ).obj (Opposite.op k) :=
    (P.lieHom.truncatedMap k ha).bchGroupMap
  have hproj (b : D.active a) : F (CompletedGroup.projection a (D.wall b).label) =
      CompletedGroup.projection k ((D.pushforward P).wall b).label :=
    (D.projection_pushforward_wall_label P k ha b).symm
  rw [D.combinedLabel_eq_noncommProd_incidentActive a θ v hθ,
    (D.pushforward P).combinedLabel_eq_noncommProd_incidentActive k]
  -- Read the truncated BCH map as the map `F` between the objects of the group towers.
  change _ = F _
  rw [Finset.map_noncommProd]
  simp only [map_zpow, hproj]
  have hs := D.map_incidentActive_pushforward_subset P k ha θ
  refine Eq.trans ?_ ((Finset.noncommProd_map _ e _ _).symm.trans
    (Finset.noncommProd_subset hs _ _ fun b hb hnot => ?_))
  · exact Finset.noncommProd_congr rfl (fun j _ => by
      simp only [coe_activePushforwardEmbedding, e,
        pos_realCharacter_pushforward_normal_iff]) _
  · simp only [D.projection_pushforward_wall_label_eq_one P k ha hb hnot, one_zpow]

/-- **Germ labels under pushforward.** The germ label of the pushforward at the image `A θ` of a
regular point and the image `A v` of a direction is the image of the germ label of `D` under the
completed Lie map. -/
theorem germLabel_pushforward {θ : V} (v : V) (hθ : D.IsRegular θ) :
    (D.pushforward P).germLabel (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v)
        (hθ.pushforward P) =
      P.lieHom.completedMap (D.germLabel θ v hθ) :=
  CompletedGroup.ext fun k => by
    rw [projection_germLabel, P.lieHom.projection_completedMap, projection_germLabel,
      ← combinedLabel_pushforward]

variable {D} {E : DirectedDiagram (d := d') h' H' κ}

/-- **Germ labels of diagrams equivalent to a pushforward.** Let `θ` be a generic point of an
affine subspace `B` for `D`, and `E` a diagram equivalent to `D.pushforward P` for which the image
`A θ` is a generic point of the image of `B`. Then for every direction `v ∉ B.direction`, the
germ label of `E` at `A θ` in the direction `A v` is the image of the germ label of `D` at `θ` in
the direction `v` under the completed Lie map. -/
theorem Equivalent.germLabel_eq_pushforward (hDE : (D.pushforward P).Equivalent E)
    {B : AffineSubspace ℝ V} {θ v : V} (hD : D.IsGenericPoint B θ)
    (hE : E.IsGenericPoint (B.map P.spatialMap.toAffineEquiv.toAffineMap) (P.spatialMap θ))
    (hv : v ∉ B.direction) :
    E.germLabel (P.spatialMap θ) (P.spatialMap.toAffineEquiv.linear v) hE.isRegular =
      P.lieHom.completedMap (D.germLabel θ v hD.isRegular) := by
  have hv' : P.spatialMap.toAffineEquiv.linear v ∉
      (B.map P.spatialMap.toAffineEquiv.toAffineMap).direction := by
    rwa [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap, Submodule.mem_map_equiv,
      LinearEquiv.symm_apply_apply]
  rw [← (hDE.germLabel_eq (hD.pushforward P) hE hv'), germLabel_pushforward]

end Mei.DirectedDiagram
