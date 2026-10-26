/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Perturbation

/-!
# Common paths preserving prescribed crossing words

Paths admissible for countably many finite polyhedral complexes can approximate
any nonempty list of interior vertices, fixing the common allowed endpoints.
If finitely many complexes already admit that vertex list, the approximation
can preserve all their signed crossing words simultaneously. For paths without
an interior vertex, stationary segments supply free vertices without changing
any crossing word. If the original endpoints are only allowed for the selected
complexes, move them along segments missing those walls before perturbing.

This combines `CommonWallComplement.exists_forall₂_dist_lt`, based on Baire's
theorem, with `Quiver.Path.exists_pos_crossingWord_eq_of_forall₂_dist_lt`.
It supplies common geometric test paths for comparing labelled wall diagrams;
no relation between the complexes, their wall intersections or their normals
is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.Convex.CommonWallComplement

variable {N V J K : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Countable J] [Finite K]
  (C : J → FinitePolyhedralComplex h)
  (a : K → J)
  (ν : ∀ k, (C (a k)).walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ k P, LinearMap.ker (ν k P) = (affineSpan ℝ (P : Set V)).direction)
  {x y : CommonWallComplement (fun j => fun P : (C j).walls => (P : Set V))}

include hν

/-- Approximate a shared vertex list by a path admissible for every complex,
fixing the endpoints and preserving the crossing words in finitely many selected
complexes. The prescribed list has at least one interior vertex. -/
theorem exists_forall₂_dist_lt_crossingWord_eq
    {l : List V} (hl : l ≠ []) {ε : ℝ} (hε : 0 < ε)
    (p : ∀ k, AdmissiblePLPath (projection (a k) x) (projection (a k) y))
    (hp : ∀ k, (p k).vertices.map WallComplement.val = x.val :: (l ++ [y.val])) :
    ∃ q : Quiver.Path x y,
      List.Forall₂ (fun u v => dist u v < ε) (x.val :: (l ++ [y.val]))
        (q.vertices.map CommonWallComplement.val) ∧
      ∀ k, ((projectionPrefunctor (a k)).mapPath q).crossingWord (ν k) =
        (p k).crossingWord (ν k) := by
  classical
  let := Fintype.ofFinite K
  have := h.finiteDimensional
  choose r hr hword using fun k =>
    (p k).exists_pos_crossingWord_eq_of_forall₂_dist_lt (ν k) (hν k)
  -- The extra index supplies a positive radius even when no words are prescribed.
  let radius : Option K → ℝ := fun k => k.elim ε r
  let δ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Option K)).Nonempty)
    radius
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).mpr
    intro k _
    cases k with
    | none => exact hε
    | some k => exact hr k
  have hδε : δ ≤ ε := Finset.inf'_le radius (Finset.mem_univ (none : Option K))
  obtain ⟨q, hq⟩ := CommonWallComplement.exists_forall₂_dist_lt
    (fun j P => (C j).isConvexPolyhedron ((C j).mem_cells_of_mem_walls P.property))
    (fun j P => (C j).finrank_direction_add_one_of_mem_walls P.property) hl hδ x y
  refine ⟨q, hq.imp (fun _ _ huv => huv.trans_le hδε), fun k => ?_⟩
  apply hword k
  rw [hp k]
  exact (vertices_projection (a k) q).symm ▸
    hq.imp (fun _ _ huv => huv.trans_le
      (Finset.inf'_le radius (Finset.mem_univ (some k))))

/-- A nonempty finite collection of admissible paths with the same ambient vertex list
has a common replacement admissible for countably many complexes and retaining
every prescribed crossing word. Stationary segments allow the original paths
to have zero or one edge. -/
theorem exists_crossingWord_eq
    (p : ∀ k, AdmissiblePLPath (projection (a k) x) (projection (a k) y))
    (k₀ : K)
    (hp : ∀ k, (p k).vertices.map WallComplement.val =
      (p k₀).vertices.map WallComplement.val) :
    ∃ q : Quiver.Path x y, ∀ k,
      ((projectionPrefunctor (a k)).mapPath q).crossingWord (ν k) =
        (p k).crossingWord (ν k) := by
  let e (k : K) : projection (a k) x ⟶ projection (a k) x :=
    ⟨WallComplement.AdmissibleSegment.refl _ (by
      intro hs
      obtain ⟨P, hP⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion
        (fun P : (C (a k)).walls => (P : Set V))
        (fun P => ((C (a k)).isConvexPolyhedron
          ((C (a k)).mem_cells_of_mem_walls P.property)).isClosed) hs)
      exact (projection (a k) x).notMem P hP)⟩
  let padded (k : K) := ((e k).toPath.cons (e k)).comp (p k)
  let l := x.val :: (p k₀).vertices.dropLast.map WallComplement.val
  have hv (k : K) : (padded k).vertices.map WallComplement.val =
      x.val :: (l ++ [y.val]) := by
    have hend := congrArg (List.map WallComplement.val) (p k₀).dropLast_append_end_eq
    simp only [List.map_append, List.map_singleton, projection_val] at hend
    simp only [padded, Quiver.Path.vertices_comp, Quiver.Path.vertices_cons,
      Quiver.Path.vertices_toPath, List.concat_eq_append, List.cons_append,
      List.nil_append, List.dropLast_cons_cons, List.dropLast_singleton,
      List.map_cons, projection_val, hp k, l, hend]
  obtain ⟨q, _, hq⟩ := exists_forall₂_dist_lt_crossingWord_eq C a ν hν
    (List.cons_ne_nil _ _) zero_lt_one padded hv
  refine ⟨q, fun k => ?_⟩
  simpa only [padded, Quiver.Path.crossingWord_comp, Quiver.Path.crossingWord_cons,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil,
    FinitePolyhedralComplex.segmentCrossingWord_self, mul_one] using hq k

omit hν in
private theorem exists_nonCrossing_projections (x : ∀ k,
    WallComplement (fun P : (C (a k)).walls => (P : Set V))) (k₀ : K)
    (hx : ∀ k, (x k).val = (x k₀).val) :
    ∃ z : CommonWallComplement (fun j => fun P : (C j).walls => (P : Set V)),
      ∀ k, ∃ _ : projection (a k) z ⟶ x k,
        WallComplement.crossings (projection (a k) z) (x k) = ∅ := by
  classical
  have := h.finiteDimensional
  have hclosed (j : J) (P : (C j).walls) : IsClosed (P : Set V) :=
    ((C j).isConvexPolyhedron ((C j).mem_cells_of_mem_walls P.property)).isClosed
  -- The simultaneous allowed locus is dense, including for nonstabilizing complexes.
  let A : (Σ j, (C j).walls) → AffineSubspace ℝ V :=
    fun p => affineSpan ℝ (p.2 : Set V)
  have hA (p : Σ j, (C j).walls) : A p ≠ ⊤ :=
    (affineSpan ℝ (p.2 : Set V)).ne_top_of_finrank_direction_add_one_eq
      ((C p.1).finrank_direction_add_one_of_mem_walls p.2.property)
  -- A neighborhood of the original endpoint admits connectors crossing no selected wall.
  let U : Set V := {z | ∀ k (P : (C (a k)).walls) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    AffineMap.lineMap z (x k).val t ∉ (P : Set V)}
  have hU : IsOpen U := by
    have hopen := isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite
      fun P : (C (a k)).walls =>
        (hclosed (a k) P).isOpen_setOf_lineMap_notMem.preimage
          (f := fun z : V => (z, (x k).val)) (continuous_id.prodMk continuous_const)
    simpa only [U, ofPred_forall, preimage_iInter, preimage_ofPred_eq] using hopen
  have hxU : (x k₀).val ∈ U := by
    intro k P t ht
    rw [← hx k, AffineMap.lineMap_same]
    exact (x k).notMem P
  obtain ⟨z, hzU, hzA⟩ := AffineSubspace.exists_mem_open_genericLocus A hA hU ⟨_, hxU⟩
  let z' : CommonWallComplement (fun j => fun P : (C j).walls => (P : Set V)) :=
    ⟨z, fun j P hz => hzA ⟨j, P⟩ (subset_affineSpan ℝ _ hz)⟩
  refine ⟨z', fun k => ?_⟩
  have havoid := hzU k
  have hc : WallComplement.crossings (projection (a k) z') (x k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨P, t⟩ ht
    have ht := (WallComplement.mem_crossings _ _ P t).mp ht
    exact havoid P t ht.1 ht.2
  refine ⟨⟨⟨?_, ?_⟩⟩, hc⟩
  · rintro P ⟨t, ht, hP⟩
    exact (havoid P t ht hP).elim
  · intro t ht hs
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion
      (fun P : (C (a k)).walls => (P : Set V))
      (hclosed (a k)) hs)
    exact havoid P t ht hP

/-- Every shared finite-order test has a replacement admissible for countably many
complexes, retaining all prescribed crossing words. The original endpoints may lie
on walls in the other complexes; they move along segments missing the selected walls. -/
theorem exists_crossingWord_eq_of_vertices_eq
    {x y : ∀ k, WallComplement (fun P : (C (a k)).walls => (P : Set V))}
    (p : ∀ k, AdmissiblePLPath (x k) (y k)) (k₀ : K)
    (hp : ∀ k, (p k).vertices.map WallComplement.val =
      (p k₀).vertices.map WallComplement.val) :
    ∃ (u v : CommonWallComplement (fun j => fun P : (C j).walls => (P : Set V)))
      (q : Quiver.Path u v), ∀ k,
        ((projectionPrefunctor (a k)).mapPath q).crossingWord (ν k) =
          (p k).crossingWord (ν k) := by
  have hx (k : K) : (x k).val = (x k₀).val := by
    have he := congrArg List.head? (hp k)
    simpa only [List.head?_map, Quiver.Path.vertices_head?, Option.map_some,
      Option.some.injEq] using he
  have hy (k : K) : (y k).val = (y k₀).val := by
    have he := congrArg List.getLast? (hp k)
    rw [List.getLast?_map, List.getLast?_map,
      List.getLast?_eq_some_getLast (p k).vertices_ne_nil,
      List.getLast?_eq_some_getLast (p k₀).vertices_ne_nil] at he
    simpa only [Quiver.Path.vertices_getLast, Option.map_some, Option.some.injEq] using he
  obtain ⟨u, hu⟩ := exists_nonCrossing_projections C a x k₀ hx
  obtain ⟨v, hv⟩ := exists_nonCrossing_projections C a y k₀ hy
  choose e he using hu
  choose f hf using hv
  let padded (k : K) := ((e k).toPath.comp (p k)).comp (Quiver.reverse (f k)).toPath
  have hpadded (k : K) : (padded k).vertices.map WallComplement.val =
      (padded k₀).vertices.map WallComplement.val := by
    simp only [padded, Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath,
      List.dropLast_cons_cons, List.dropLast_singleton, List.cons_append,
      List.nil_append, List.map_cons, List.map_append, projection_val,
      List.map_dropLast, hp k, hy k]
    rfl
  obtain ⟨q, hq⟩ := exists_crossingWord_eq C a ν hν padded k₀ hpadded
  refine ⟨u, v, q, fun k => ?_⟩
  have heword := (C (a k)).segmentCrossingWord_eq_one (ν k) (e k) (he k)
  have hfword := (C (a k)).segmentCrossingWord_eq_one (ν k) (f k) (hf k)
  simpa only [padded, Quiver.Path.crossingWord_comp, Quiver.Path.crossingWord_cons,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil,
    FinitePolyhedralComplex.segmentCrossingWord_reverse _ _ (hν k), heword, hfword,
    inv_one, mul_one, one_mul] using hq k

end Mei.Convex.CommonWallComplement
