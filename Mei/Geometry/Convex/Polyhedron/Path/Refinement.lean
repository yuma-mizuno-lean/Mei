/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Comparison

/-!
# Products along refined wall families

Let a finite wall family `W'` refine a finite wall family `W` along an index map `f`:
each wall `W' j` lies in `W (f j)`, every wall `W i` is covered by the walls assigned
to it, and walls assigned to the same index have pairwise disjoint relative interiors.
If the refined walls carry the normals and labels of the walls they are assigned to,
then a segment admissible for both families has the same crossing times for both, and
at each time the refined signed event maps bijectively onto the coarse one. Hence each
combined simultaneous crossing label, each segment product and each polygonal product
is unchanged.

The two families need not be related by an injective restriction, so this complements
`Quiver.Path.wallPathProduct_restrict`. Coincident coarse walls may be refined separately,
and a refined wall may carry an arbitrary polyhedral support inside its coarse wall.
Bijectivity on events uses that an admissible segment crosses each wall in its relative
interior (`WallComplement.AdmissibleSegment.crossing_mem_intrinsicInterior`).
-/

public section

noncomputable section

open Set

namespace Mei.Convex.WallComplement

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V} {W' : κ → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
  (ν' : κ → V →ₗ[ℝ] ℝ) (label' : κ → G)
  (hcomm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))
  {f : κ → ι} (hsub : ∀ j, W' j ⊆ W (f j)) (hcover : ∀ i, W i ⊆ ⋃ j ∈ f ⁻¹' {i}, W' j)
  (hdisj : ∀ i, (f ⁻¹' {i}).PairwiseDisjoint fun j => intrinsicInterior ℝ (W' j))
  (hν : ∀ j, ν' j = ν (f j)) (hlabel : ∀ j, label' j = label (f j))
  {x y : WallComplement W} {x' y' : WallComplement W'}

omit [Finite ι] [Finite κ] in
include hsub hcover in
/-- A segment meets a coarse wall exactly when it meets one of the walls assigned to it. -/
private theorem mem_crossings_iff_of_refines (hx : x'.val = x.val) (hy : y'.val = y.val)
    (i : ι) (t : ℝ) :
    (i, t) ∈ crossings x y ↔ ∃ j, f j = i ∧ (j, t) ∈ crossings x' y' := by
  simp only [mem_crossings, hx, hy]
  constructor
  · rintro ⟨ht, hi⟩
    obtain ⟨j, hj, hz⟩ := mem_iUnion₂.mp (hcover i hi)
    exact ⟨j, by simpa using hj, ht, hz⟩
  · rintro ⟨j, rfl, ht, hj⟩
    exact ⟨ht, hsub j hj⟩

omit [Finite ι] [Finite κ] in
include hdisj in
/-- An admissible segment crosses at most one of the walls assigned to a coarse wall
at any given time. -/
private theorem eq_of_mem_crossings_of_refines (e' : x' ⟶ y') {j₁ j₂ : κ} {t : ℝ}
    (h₁ : (j₁, t) ∈ crossings x' y') (h₂ : (j₂, t) ∈ crossings x' y') (hf : f j₁ = f j₂) :
    j₁ = j₂ := by
  by_contra hne
  obtain ⟨ht, hz₁⟩ := (mem_crossings x' y' j₁ t).mp h₁
  obtain ⟨-, hz₂⟩ := (mem_crossings x' y' j₂ t).mp h₂
  exact Set.disjoint_left.mp (hdisj (f j₂) (by simpa using hf) rfl hne)
    (e'.down.crossing_mem_intrinsicInterior ht hz₁).2
    (e'.down.crossing_mem_intrinsicInterior ht hz₂).2

include hsub hcover hν in
/-- Each coarse signed event is the image of the refined signed event at the same time. -/
theorem signedCrossingEvent_eq_image_of_refines [DecidableEq ι]
    (hx : x'.val = x.val) (hy : y'.val = y.val) (t : ℝ) :
    signedCrossingEvent ν x y t = (signedCrossingEvent ν' x' y' t).image (Prod.map f id) := by
  ext ⟨i, s⟩
  simp only [mem_signedCrossingEvent, Finset.mem_image, Prod.exists, Prod.map_apply, id_eq,
    Prod.mk.injEq, mem_crossings_iff_of_refines hsub hcover hx hy]
  constructor
  · rintro ⟨⟨j, rfl, hj⟩, rfl⟩
    exact ⟨j, _, ⟨hj, rfl⟩, rfl, by rw [hν, hx, hy]⟩
  · rintro ⟨j, r, ⟨hj, rfl⟩, rfl, rfl⟩
    exact ⟨⟨j, rfl, hj⟩, by rw [hν, hx, hy]⟩

include hsub hcover hdisj hν hlabel in
/-- Refinement preserves the combined label of every simultaneous crossing. -/
theorem crossingEventProduct_eq_of_refines (e : x ⟶ y) (e' : x' ⟶ y')
    (hx : x'.val = x.val) (hy : y'.val = y.val) (t : ℝ) :
    crossingEventProduct ν' label' hcomm' e' t = crossingEventProduct ν label hcomm e t := by
  classical
  let S := signedCrossingEvent ν' x' y' t
  have hinj : ∀ a ∈ S.toList, ∀ b ∈ S.toList, Prod.map f id a = Prod.map f id b → a = b := by
    rintro ⟨j₁, s₁⟩ h₁ ⟨j₂, s₂⟩ h₂ he
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at he
    have h₁ := ((mem_signedCrossingEvent _ _ _ _ _ _).mp (Finset.mem_toList.mp h₁)).1
    have h₂ := ((mem_signedCrossingEvent _ _ _ _ _ _).mp (Finset.mem_toList.mp h₂)).1
    rw [eq_of_mem_crossings_of_refines hdisj e' h₁ h₂ he.1, he.2]
  rw [crossingEventProduct_eq_prod ν' label' hcomm' e' t S.toList (Finset.nodup_toList S)
      (fun _ => Finset.mem_toList),
    crossingEventProduct_eq_prod ν label hcomm e t (S.toList.map (Prod.map f id))
      ((Finset.nodup_toList S).map_on hinj) (fun a => by
        rw [signedCrossingEvent_eq_image_of_refines ν ν' hsub hcover hν hx hy t, List.mem_map,
          Finset.mem_image]
        simp only [Finset.mem_toList, S])]
  simp only [List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, hlabel]

include hsub hcover in
/-- Refinement preserves the ordered crossing times of a segment. -/
theorem orderedCrossingTimes_eq_of_refines (e : x ⟶ y) (e' : x' ⟶ y')
    (hx : x'.val = x.val) (hy : y'.val = y.val) :
    orderedCrossingTimes e' = orderedCrossingTimes e := by
  refine (pairwise_orderedCrossingTimes e').eq_of_mem_iff (pairwise_orderedCrossingTimes e)
    fun t => ?_
  simp only [mem_orderedCrossingTimes, mem_crossings_iff_of_refines hsub hcover hx hy]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨f j, j, rfl, hj⟩
  · rintro ⟨_, j, -, hj⟩
    exact ⟨j, hj⟩

include hsub hcover hdisj hν hlabel in
/-- Refinement preserves the transport along a segment admissible for both families. -/
theorem segmentPathProduct_eq_of_refines (e : x ⟶ y) (e' : x' ⟶ y')
    (hx : x'.val = x.val) (hy : y'.val = y.val) :
    segmentPathProduct ν' label' hcomm' e' = segmentPathProduct ν label hcomm e := by
  have hevent : crossingEventProduct ν' label' hcomm' e' = crossingEventProduct ν label hcomm e :=
    funext (crossingEventProduct_eq_of_refines ν label hcomm ν' label' hcomm' hsub hcover hdisj
      hν hlabel e e' hx hy)
  rw [segmentPathProduct_def, segmentPathProduct_def, hevent,
    orderedCrossingTimes_eq_of_refines hsub hcover e e' hx hy]

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex WallComplement

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V} {W' : κ → Set V}

/-- A polygonal path admissible for a family and for a refinement of it has the same
transport in both, when refined walls carry the normals and labels of their coarse walls. -/
theorem wallPathProduct_eq_of_refines (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (ν' : κ → V →ₗ[ℝ] ℝ) (label' : κ → G)
    (hcomm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))
    {f : κ → ι} (hsub : ∀ j, W' j ⊆ W (f j)) (hcover : ∀ i, W i ⊆ ⋃ j ∈ f ⁻¹' {i}, W' j)
    (hdisj : ∀ i, (f ⁻¹' {i}).PairwiseDisjoint fun j => intrinsicInterior ℝ (W' j))
    (hν : ∀ j, ν' j = ν (f j)) (hlabel : ∀ j, label' j = label (f j))
    {x y : WallComplement W} {x' y' : WallComplement W'}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : q.vertices.map WallComplement.val = p.vertices.map WallComplement.val) :
    q.wallPathProduct ν' label' hcomm' = p.wallPathProduct ν label hcomm := by
  symm
  exact wallPathProduct_eq_of_segmentPathProduct_eq ν label hcomm ν' label' hcomm'
    (fun e e' hx hy => (segmentPathProduct_eq_of_refines ν label hcomm ν' label' hcomm'
      hsub hcover hdisj hν hlabel e e' hx.symm hy.symm).symm) p q hpq.symm

end Quiver.Path
