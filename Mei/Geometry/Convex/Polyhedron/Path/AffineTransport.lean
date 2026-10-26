/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Map
public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Affine transport of simultaneous wall products

An affine equivalence and a bijection of wall indices preserve the ordered
crossing times and the full signed sets of simultaneous crossings. Pull normals
back along the linear part, and carry labels along a group homomorphism: the
transported polygonal product is the image of the original product. Coincident
indexed walls remain distinct factors, so this applies to overlapping wall
families as well as to walls of a complex.

This combines `ContinuousAffineEquiv.wallComplementMap`, the signed events of
`Mei.Convex.WallComplement`, and `Finset.noncommProd_map`. Commutation is required
only for labels whose supports have the same affine span; labels at different
crossing times need not commute. No polyhedrality or lattice is required.
-/

public section

noncomputable section

open Set Mei.Convex Mei.Convex.WallComplement

namespace ContinuousAffineEquiv

variable {V V' ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [Finite ι] [Finite ι']
  {W : ι → Set V} {W' : ι' → Set V'}
  (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι') (hW : ∀ j, W' (r j) = e '' W j)
  {x y : WallComplement W}

/-- Affine transport preserves the distinct crossing times in their original order. -/
@[simp]
theorem orderedCrossingTimes_wallComplementMap (a : x ⟶ y) :
    orderedCrossingTimes ((e.wallComplementMap r hW).map a) = orderedCrossingTimes a := by
  apply (pairwise_orderedCrossingTimes _).eq_of_mem_iff (pairwise_orderedCrossingTimes a)
  intro t
  simp only [mem_orderedCrossingTimes]
  exact r.symm.exists_congr_left.trans (exists_congr fun j =>
    e.mem_crossings_wallComplementMap r hW x y j t)

variable (ν : ι → V →ₗ[ℝ] ℝ) (ν' : ι' → V' →ₗ[ℝ] ℝ)
  (hν : ∀ j, (ν' (r j)).comp e.toAffineEquiv.linear.toLinearMap = ν j)

include hν

/-- Every simultaneous signed event is carried by the wall bijection, with
its exponents unchanged, including under orientation-reversing affine maps. -/
@[simp]
theorem signedCrossingEvent_wallComplementMap (x y : WallComplement W) (t : ℝ) :
    signedCrossingEvent ν' ((e.wallComplementMap r hW).obj x)
        ((e.wallComplementMap r hW).obj y) t =
      (signedCrossingEvent ν x y t).map
        (Equiv.prodCongr r (Equiv.refl ℤ)).toEmbedding := by
  classical
  ext ⟨j, s⟩
  obtain ⟨j, rfl⟩ := r.surjective j
  have hv : ν' (r j) (e y.val - e x.val) = ν j (y.val - x.val) := by
    have hsub : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe,
        ContinuousAffineEquiv.coe_coe, LinearEquiv.coe_coe, vsub_eq_sub] using
        e.toAffineEquiv.toAffineMap.linear_apply_vsub y.val x.val
    rw [← hsub]
    exact LinearMap.congr_fun (hν j) _
  simp only [Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.symm_apply_apply, Equiv.refl_symm, Equiv.refl_apply,
    mem_signedCrossingEvent, wallComplementMap_obj_val,
    e.mem_crossings_wallComplementMap r hW x y j t, hv]

/-- Segment event lists retain their order and all simultaneous indices. -/
@[simp]
theorem segmentCrossingEvents_wallComplementMap (a : x ⟶ y) :
    segmentCrossingEvents ν' ((e.wallComplementMap r hW).map a) =
      (segmentCrossingEvents ν a).map
        (fun S => S.map (Equiv.prodCongr r (Equiv.refl ℤ)).toEmbedding) := by
  simp only [segmentCrossingEvents_def, orderedCrossingTimes_wallComplementMap,
    List.map_map, Function.comp_def]
  exact List.map_congr_left fun t _ => e.signedCrossingEvent_wallComplementMap r hW ν ν' hν x y t

variable {G K : Type*} [Group G] [Group K]
  (label : ι → G) (label' : ι' → K)
  (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
  (comm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))
  (f : G →* K) (hlabel : ∀ j, label' (r j) = f (label j))

include hlabel

/-- The product of all labels at one time commutes with affine transport and
coefficient change, without choosing an enumeration of coincident walls. -/
theorem crossingEventProduct_wallComplementMap (a : x ⟶ y) (t : ℝ) :
    crossingEventProduct ν' label' comm' ((e.wallComplementMap r hW).map a) t =
      f (crossingEventProduct ν label comm a t) := by
  have hc := signedCrossingEvent_pairwise ν' label' comm'
    ((e.wallComplementMap r hW).map a) t
  rw [e.signedCrossingEvent_wallComplementMap r hW ν ν' hν x y t] at hc
  calc
    _ = (signedCrossingEvent ν' ((e.wallComplementMap r hW).obj x)
        ((e.wallComplementMap r hW).obj y) t).noncommProd
        (fun b => label' b.1 ^ b.2)
        (signedCrossingEvent_pairwise ν' label' comm' ((e.wallComplementMap r hW).map a) t) :=
      crossingEventProduct_eq_noncommProd _ _ _ _ _ _
    _ = ((signedCrossingEvent ν x y t).map
        (Equiv.prodCongr r (Equiv.refl ℤ)).toEmbedding).noncommProd
        (fun b => label' b.1 ^ b.2) hc := by
      exact Finset.noncommProd_congr
        (e.signedCrossingEvent_wallComplementMap r hW ν ν' hν x y t)
        (fun _ _ => rfl) _
    _ = _ := Finset.noncommProd_map _ _ _ hc
    _ = _ := by
      rw [crossingEventProduct_eq_noncommProd ν label comm a t
        (signedCrossingEvent_pairwise ν label comm a t), Finset.map_noncommProd]
      apply Finset.noncommProd_congr rfl
      intro b _
      simp only [Equiv.toEmbedding_apply, Equiv.prodCongr_apply, Prod.map_fst,
        Prod.map_snd, Equiv.refl_apply, hlabel, map_zpow]

/-- Affine transport and coefficient change preserve the reverse-time segment product. -/
theorem segmentPathProduct_wallComplementMap (a : x ⟶ y) :
    segmentPathProduct ν' label' comm' ((e.wallComplementMap r hW).map a) =
      f (segmentPathProduct ν label comm a) := by
  simp only [segmentPathProduct_def, orderedCrossingTimes_wallComplementMap,
    map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t _
  exact e.crossingEventProduct_wallComplementMap r hW ν ν' hν label label' comm comm' f hlabel a t

end ContinuousAffineEquiv

namespace Quiver.Path

variable {V V' ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [Finite ι] [Finite ι']
  {W : ι → Set V} {W' : ι' → Set V'}
  {x y : WallComplement W}
  (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι')
  (hW : ∀ j, W' (r j) = e '' W j)
  (ν : ι → V →ₗ[ℝ] ℝ) (ν' : ι' → V' →ₗ[ℝ] ℝ)
  (hν : ∀ j, (ν' (r j)).comp e.toAffineEquiv.linear.toLinearMap = ν j)

include hν

/-- Affine transport preserves all signed events along a polygonal path,
including separate visits to the same wall. -/
@[simp]
theorem signedCrossingEvents_wallComplementMap :
    ((e.wallComplementMap r hW).mapPath p).signedCrossingEvents ν' =
      (p.signedCrossingEvents ν).map
        (fun S => S.map (Equiv.prodCongr r (Equiv.refl ℤ)).toEmbedding) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp only [Prefunctor.mapPath_cons, signedCrossingEvents_cons, ih, List.map_append,
      e.segmentCrossingEvents_wallComplementMap r hW ν ν' hν a]

/-- Transporting supports, coorientations and labels carries the full wall
product through a group homomorphism. This includes arbitrary simultaneous
coplanar crossings and affine equivalences of either orientation. -/
theorem wallPathProduct_wallComplementMap {G K : Type*} [Group G] [Group K]
    (label : ι → G) (label' : ι' → K)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (comm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))
    (f : G →* K) (hlabel : ∀ j, label' (r j) = f (label j)) :
    ((e.wallComplementMap r hW).mapPath p).wallPathProduct ν' label' comm' =
      f (p.wallPathProduct ν label comm) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp only [Prefunctor.mapPath_cons, wallPathProduct_cons, ih, map_mul,
      e.segmentPathProduct_wallComplementMap r hW ν ν' hν label label' comm comm' f hlabel a]

end Quiver.Path
