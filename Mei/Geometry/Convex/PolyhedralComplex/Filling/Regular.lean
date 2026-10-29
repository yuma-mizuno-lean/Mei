/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport
public import Mei.Geometry.Convex.PolyhedralComplex.Sampling
public import Mei.Geometry.Convex.Polyhedron.Filling
import Mathlib.Tactic.FunProp

/-!
# Crossing words of regular affine fillings

A continuous square avoiding singular support, with affine admissible sides,
has trivial boundary crossing word. Filling a triangle gives the local segment
cocycle: transport along two sides agrees with transport along the direct side.
This identity holds in the free group of walls, so it may be evaluated under
arbitrary group-valued wall labels, including noncommuting ones. It supplies the
local compatibility needed to transport coefficients across regular wall points.
-/

-- The proof uses `Mei.Convex.exists_admissible_filling_grid_fixed_boundary`,
-- `FinitePolyhedralComplex.exists_ball_crossingWord_eq`, the normal-closure grid
-- boundary theorem, and `segmentCrossingWord_eq_prod_sampling`. Each grid cell
-- lies in a regular transport neighborhood, and a triangle is represented by
-- a square filling with one constant side.


public noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)

/-- A square filled in the complement of singular support has trivial boundary
word. Its sides are the given affine segments; neither the square nor its sides
need be embedded or nondegenerate. No consistency or label relations are assumed. -/
theorem crossingWord_boundary_eq_one_of_regular_filling
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
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
    (hreg : ∀ z, f z ∉ singularSupport (fun P : C.walls => (P : Set V))) :
    ((((e₁ 0).toPath.cons (e₂ 1)).cons (Quiver.reverse (e₁ 1))).cons
      (Quiver.reverse (e₂ 0))).crossingWord ν = 1 := by
  classical
  have := h.finiteDimensional
  choose r hr hlocal using fun z => C.exists_ball_crossingWord_eq ν hν (hreg z)
  obtain ⟨n, t, -, ht0, htmono, ht1, v, hboundary, -, e, g, hgrid⟩ :=
    exists_admissible_filling_grid_fixed_boundary
      (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      x e₁ e₂ f hf₁ hf₂ (fun z => Metric.ball (f z) (r z))
      (fun _ => Metric.isOpen_ball) (fun z => ⟨z, Metric.mem_ball_self (hr z)⟩)
      (η := 1) zero_lt_one
  let cell := fun a b => (((e a b.castSucc).toPath.cons (g a.succ b)).cons
    (Quiver.reverse (e a b.succ))).cons (Quiver.reverse (g a.castSucc b))
  have hcell (a b : Fin n) : (cell a b).crossingWord ν = 1 := by
    obtain ⟨j, -, hj⟩ := hgrid a b
    have hp : ∀ z ∈ (cell a b).vertices, z.val ∈ Metric.ball (f j) (r j) := by
      intro z hz
      obtain ⟨c, rfl⟩ := Quiver.Path.grid_cell_vertices_subset_range v e g a b z hz
      exact hj (subset_convexHull ℝ _ (mem_range_self c))
    exact (hlocal j _ _ (cell a b) .nil hp (by
      intro z hz
      have he : z = v (a.castSucc, b.castSucc) := by simpa using hz
      subst z
      exact hp _ (cell a b).start_mem_vertices)).trans (Quiver.Path.crossingWord_nil ν)
  have hnormal : Subgroup.normalClosure
      {w | ∃ a b : Fin n, w = (cell a b).crossingWord ν} ≤ ⊥ := by
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨a, b, rfl⟩
    exact Subgroup.mem_bot.mpr (hcell a b)
  have hmem := hnormal (C.crossingWord_grid_boundary_mem_normalClosure ν hν v e g)
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
  simpa only [Subgroup.mem_bot, Quiver.Path.crossingWord_cons,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil, mul_one,
    C.segmentCrossingWord_reverse ν hν, mul_assoc] using hmem

/-- Two successive affine segments across a singularity-free filled triangle
have the same crossing word as its third side. This is an equality in the free
group, so arbitrary noncommuting wall labels inherit the segment cocycle law. -/
theorem segmentCrossingWord_mul_eq_of_regular_triangle
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    {y z w : WallComplement (fun P : C.walls => (P : Set V))}
    (e : y ⟶ z) (g : z ⟶ w) (d : y ⟶ w)
    (hreg : Disjoint (convexHull ℝ {y.val, z.val, w.val})
      (singularSupport (fun P : C.walls => (P : Set V)))) :
    C.segmentCrossingWord ν g * C.segmentCrossingWord ν e =
      C.segmentCrossingWord ν d := by
  classical
  have hy : y.val ∈ convexHull ℝ {y.val, z.val, w.val} := subset_convexHull ℝ _ (by simp)
  have hz : z.val ∈ convexHull ℝ {y.val, z.val, w.val} := subset_convexHull ℝ _ (by simp)
  have hw : w.val ∈ convexHull ℝ {y.val, z.val, w.val} := subset_convexHull ℝ _ (by simp)
  have hconv := convex_convexHull ℝ ({y.val, z.val, w.val} : Set V)
  let x : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)) :=
    fun p => if p.1 = 0 then y else if p.2 = 0 then z else w
  let e₁ (b : Fin 2) : x (0, b) ⟶ x (1, b) := PLift.up (by
    by_cases hb : b = 0
    · simpa [x, hb] using e.down
    · simpa [x, hb] using d.down)
  let e₂ (a : Fin 2) : x (a, 0) ⟶ x (a, 1) := PLift.up (by
    by_cases ha : a = 0
    · simpa [x, ha] using WallComplement.AdmissibleSegment.refl y
        (fun hh => Set.disjoint_left.mp hreg hy hh)
    · simpa [x, ha] using g.down)
  let f : C(↥unitInterval × ↥unitInterval, V) :=
    ⟨fun p => AffineMap.lineMap
      (AffineMap.lineMap y.val z.val (p.1 : ℝ))
      (AffineMap.lineMap y.val w.val (p.1 : ℝ)) (p.2 : ℝ), by
        simp only [AffineMap.lineMap_apply_module']
        fun_prop⟩
  have hf₁ (b : Fin 2) (s : unitInterval) : f (s, if b = 0 then 0 else 1) =
      AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ) := by
    by_cases hb : b = 0 <;> simp [f, x, hb]
  have hf₂ (a : Fin 2) (s : unitInterval) : f (if a = 0 then 0 else 1, s) =
      AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ) := by
    by_cases ha : a = 0 <;> simp [f, x, ha]
  have hfreg (p) : f p ∉ singularSupport (fun P : C.walls => (P : Set V)) :=
    Set.disjoint_left.mp hreg (hconv.lineMap_mem
      (hconv.lineMap_mem hy hz p.1.property)
      (hconv.lineMap_mem hy hw p.1.property) p.2.property)
  have hb := C.crossingWord_boundary_eq_one_of_regular_filling ν hν x e₁ e₂ f hf₁ hf₂ hfreg
  have hself : C.segmentCrossingWord ν (e₂ 0) = 1 := by
    apply C.segmentCrossingWord_self
  simp only [Quiver.Path.crossingWord_cons, C.segmentCrossingWord_reverse ν hν,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil, mul_one, hself, inv_one, one_mul] at hb
  -- The side constructors lift only admissibility proofs. Proof irrelevance
  -- identifies these with the supplied edges, including their exact endpoints.
  have he₁0 : C.segmentCrossingWord ν (e₁ 0) = C.segmentCrossingWord ν e := (rfl)
  have he₁1 : C.segmentCrossingWord ν (e₁ 1) = C.segmentCrossingWord ν d := (rfl)
  have he₂1 : C.segmentCrossingWord ν (e₂ 1) = C.segmentCrossingWord ν g := (rfl)
  rw [he₁0, he₁1, he₂1] at hb
  have htri : (C.segmentCrossingWord ν d)⁻¹ *
      (C.segmentCrossingWord ν g * C.segmentCrossingWord ν e) = 1 := by
    simpa only [mul_assoc] using hb
  exact (inv_mul_eq_one.mp htri).symm

end Mei.FinitePolyhedralComplex
