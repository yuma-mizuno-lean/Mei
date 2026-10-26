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
any crossing word.

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

end Mei.Convex.CommonWallComplement
