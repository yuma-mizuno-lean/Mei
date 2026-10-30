/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Sampling
public import Mei.Geometry.Convex.Polyhedron.Filling
import Mathlib.Tactic.FunProp

/-!
# Boundary words of fillings from local relations

Fix a normal subgroup `K` of the free group on the walls of a finite polyhedral complex.
Suppose a continuous square with affine admissible sides is covered by open sets, in each of
which every admissible polygonal loop has crossing word in `K`. Then the boundary word of the
square lies in `K`. A filled triangle, viewed as a square with one constant side, has the
same property. Neither the square nor the triangle needs to be embedded or nondegenerate,
and their boundary edges are kept fixed.

This reduces global relations among crossing words to local ones. Regular neighbourhoods,
where crossing words are path independent, give `K = ⊥`; isolating joint neighbourhoods give
the normal closure of the joint meridians.

The proof subdivides the square by `Mei.Convex.exists_admissible_filling_grid_fixed_boundary`,
places each grid cell in one of the open sets, and combines
`FinitePolyhedralComplex.crossingWord_grid_boundary_mem_normalClosure` with
`FinitePolyhedralComplex.segmentCrossingWord_eq_prod_sampling_of_endpoints` on the four sides.
-/

public noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)

/-- Let a continuous square with the given affine admissible sides be covered by open sets in
which every admissible loop has crossing word in a normal subgroup `K`. Then the boundary word
of the square lies in `K`. -/
theorem crossingWord_boundary_mem_of_cover
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (K : Subgroup (FreeGroup C.walls)) [K.Normal]
    (x : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)))
    (e₁ : ∀ b : Fin 2, x (0, b) ⟶ x (1, b))
    (e₂ : ∀ a : Fin 2, x (a, 0) ⟶ x (a, 1))
    (f : C(↥unitInterval × ↥unitInterval, V))
    (hf₁ : ∀ (b : Fin 2) (s : unitInterval),
      f (s, if b = 0 then 0 else 1) =
        AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ))
    (hf₂ : ∀ (a : Fin 2) (s : unitInterval),
      f (if a = 0 then 0 else 1, s) =
        AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ))
    {κ : Type*} (U : κ → Set V) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ z, ∃ j, f z ∈ U j)
    (hlocal : ∀ j (y : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath y y), (∀ w ∈ p.vertices, w.val ∈ U j) → p.crossingWord ν ∈ K) :
    ((((e₁ 0).toPath.cons (e₂ 1)).cons (Quiver.reverse (e₁ 1))).cons
      (Quiver.reverse (e₂ 0))).crossingWord ν ∈ K := by
  classical
  have := h.finiteDimensional
  obtain ⟨n, t, -, ht0, htmono, ht1, v, hboundary, -, e, g, hgrid⟩ :=
    exists_admissible_filling_grid_fixed_boundary
      (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      x e₁ e₂ f hf₁ hf₂ U hU hcover (η := 1) zero_lt_one
  let cell := fun a b => (((e a b.castSucc).toPath.cons (g a.succ b)).cons
    (Quiver.reverse (e a b.succ))).cons (Quiver.reverse (g a.castSucc b))
  -- Every grid cell lies in one of the open sets, where the local hypothesis applies.
  have hnormal : Subgroup.normalClosure
      {w | ∃ a b : Fin n, w = (cell a b).crossingWord ν} ≤ K := by
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨a, b, rfl⟩
    obtain ⟨j, -, hj⟩ := hgrid a b
    refine hlocal j _ (cell a b) fun z hz => ?_
    obtain ⟨c, rfl⟩ := Quiver.Path.grid_cell_vertices_subset_range v e g a b z hz
    exact hj (subset_convexHull ℝ _ (mem_range_self c))
  have hmem := hnormal (C.crossingWord_grid_boundary_mem_normalClosure ν hν v e g)
  -- The four sides of the grid sample the four original edges.
  have hrow (b : Fin 2) : C.segmentCrossingWord ν (e₁ b) =
      (List.ofFn (fun a : Fin n => C.segmentCrossingWord ν
        (e a (if b = 0 then 0 else Fin.last n)))).reverse.prod := by
    apply C.segmentCrossingWord_eq_prod_sampling_of_endpoints ν (e₁ b)
      (fun a => v (a, if b = 0 then 0 else Fin.last n)) (fun a => t a.val)
      ht0 ht1 (fun _ _ hab => htmono hab)
    intro a
    rw [hboundary _ (by split_ifs <;> simp)]
    by_cases hb : b = 0
    · simpa [hb, ht0] using hf₁ b (t a.val)
    · simpa [hb, ht1] using hf₁ b (t a.val)
  have hcol (a : Fin 2) : C.segmentCrossingWord ν (e₂ a) =
      (List.ofFn (fun b : Fin n => C.segmentCrossingWord ν
        (g (if a = 0 then 0 else Fin.last n) b))).reverse.prod := by
    apply C.segmentCrossingWord_eq_prod_sampling_of_endpoints ν (e₂ a)
      (fun b => v (if a = 0 then 0 else Fin.last n, b)) (fun b => t b.val)
      ht0 ht1 (fun _ _ hab => htmono hab)
    intro b
    rw [hboundary _ (by split_ifs <;> simp)]
    by_cases ha : a = 0
    · simpa [ha, ht0] using hf₂ a (t b.val)
    · simpa [ha, ht1] using hf₂ a (t b.val)
  have hrow0 : C.segmentCrossingWord ν (e₁ 0) =
      (List.ofFn (fun a : Fin n => C.segmentCrossingWord ν (e a 0))).reverse.prod := hrow 0
  have hrow1 : C.segmentCrossingWord ν (e₁ 1) =
      (List.ofFn (fun a : Fin n => C.segmentCrossingWord ν (e a (Fin.last n)))).reverse.prod :=
    hrow 1
  have hcol0 : C.segmentCrossingWord ν (e₂ 0) =
      (List.ofFn (fun b : Fin n => C.segmentCrossingWord ν (g 0 b))).reverse.prod := hcol 0
  have hcol1 : C.segmentCrossingWord ν (e₂ 1) =
      (List.ofFn (fun b : Fin n => C.segmentCrossingWord ν (g (Fin.last n) b))).reverse.prod :=
    hcol 1
  dsimp only at hmem
  rw [← hrow0, ← hrow1, ← hcol0, ← hcol1] at hmem
  simpa only [Quiver.Path.crossingWord_cons, Quiver.Hom.toPath, Quiver.Path.crossingWord_nil,
    mul_one, C.segmentCrossingWord_reverse ν hν, mul_assoc] using hmem

/-- Let the filled triangle of an admissible triangular loop be covered by open sets in which
every admissible loop has crossing word in a normal subgroup `K`. Then the word of the
triangular loop lies in `K`. The triangle may be degenerate. -/
theorem crossingWord_triangle_mem_of_cover
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (K : Subgroup (FreeGroup C.walls)) [K.Normal]
    {x y z : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) (f : y ⟶ z) (r : z ⟶ x)
    {κ : Type*} (U : κ → Set V) (hU : ∀ j, IsOpen (U j))
    (hcover : convexHull ℝ {x.val, y.val, z.val} ⊆ ⋃ j, U j)
    (hlocal : ∀ j (w : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath w w), (∀ u ∈ p.vertices, u.val ∈ U j) → p.crossingWord ν ∈ K) :
    ((e.toPath.cons f).cons r).crossingWord ν ∈ K := by
  classical
  have hx : x.val ∈ convexHull ℝ {x.val, y.val, z.val} := subset_convexHull ℝ _ (by simp)
  have hy : y.val ∈ convexHull ℝ {x.val, y.val, z.val} := subset_convexHull ℝ _ (by simp)
  have hz : z.val ∈ convexHull ℝ {x.val, y.val, z.val} := subset_convexHull ℝ _ (by simp)
  have hconv := convex_convexHull ℝ ({x.val, y.val, z.val} : Set V)
  -- View the triangle as a square whose side at the first vertex is constant.
  let X : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)) :=
    fun p => if p.1 = 0 then x else if p.2 = 0 then y else z
  let e₁ (b : Fin 2) : X (0, b) ⟶ X (1, b) := PLift.up (by
    by_cases hb : b = 0
    · simpa [X, hb] using e.down
    · simpa [X, hb] using r.down.symm)
  let e₂ (a : Fin 2) : X (a, 0) ⟶ X (a, 1) := PLift.up (by
    by_cases ha : a = 0
    · have hxs : x.val ∉ singularSupport (fun P : C.walls => (P : Set V)) := fun hs => by
        obtain ⟨P, hP⟩ := mem_iUnion.mp (singularSupport_subset_iUnion _
          (fun P => (C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property)).isClosed) hs)
        exact x.notMem P hP
      simpa [X, ha] using WallComplement.AdmissibleSegment.refl x hxs
    · simpa [X, ha] using f.down)
  let F : C(↥unitInterval × ↥unitInterval, V) :=
    ⟨fun p => AffineMap.lineMap
      (AffineMap.lineMap x.val y.val (p.1 : ℝ))
      (AffineMap.lineMap x.val z.val (p.1 : ℝ)) (p.2 : ℝ), by
        simp only [AffineMap.lineMap_apply_module']
        fun_prop⟩
  have hF₁ (b : Fin 2) (s : unitInterval) : F (s, if b = 0 then 0 else 1) =
      AffineMap.lineMap (X (0, b)).val (X (1, b)).val (s : ℝ) := by
    by_cases hb : b = 0 <;> simp [F, X, hb]
  have hF₂ (a : Fin 2) (s : unitInterval) : F (if a = 0 then 0 else 1, s) =
      AffineMap.lineMap (X (a, 0)).val (X (a, 1)).val (s : ℝ) := by
    by_cases ha : a = 0 <;> simp [F, X, ha]
  have hFcover (p) : ∃ j, F p ∈ U j := mem_iUnion.mp (hcover (hconv.lineMap_mem
    (hconv.lineMap_mem hx hy p.1.property) (hconv.lineMap_mem hx hz p.1.property)
    p.2.property))
  have hb := C.crossingWord_boundary_mem_of_cover ν hν K X e₁ e₂ F hF₁ hF₂ U hU hFcover hlocal
  have hself : C.segmentCrossingWord ν (e₂ 0) = 1 := C.segmentCrossingWord_self ν _
  -- The side constructors lift only admissibility proofs. Proof irrelevance
  -- identifies these with the supplied edges, including their exact endpoints.
  have he₁0 : C.segmentCrossingWord ν (e₁ 0) = C.segmentCrossingWord ν e := (rfl)
  have he₁1 : C.segmentCrossingWord ν (e₁ 1) =
      C.segmentCrossingWord ν (Quiver.reverse r) := (rfl)
  have he₂1 : C.segmentCrossingWord ν (e₂ 1) = C.segmentCrossingWord ν f := (rfl)
  simp only [Quiver.Path.crossingWord_cons, C.segmentCrossingWord_reverse ν hν,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil, mul_one, hself, inv_one, one_mul,
    he₁0, he₁1, he₂1, inv_inv] at hb ⊢
  simpa only [mul_assoc] using hb

end Mei.FinitePolyhedralComplex
