/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport
public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Local

/-!
# Crossing words of regular affine fillings

A continuous square avoiding singular support, with affine admissible sides,
has trivial boundary crossing word. Filling a triangle gives the local segment
cocycle: transport along two sides agrees with transport along the direct side.
This identity holds in the free group of walls, so it may be evaluated under
arbitrary group-valued wall labels, including noncommuting ones. It supplies the
local compatibility needed to transport coefficients across regular wall points.
-/

-- The proofs apply `FinitePolyhedralComplex.crossingWord_boundary_mem_of_cover` and
-- `FinitePolyhedralComplex.crossingWord_triangle_mem_of_cover` with the trivial subgroup,
-- covering the filling by the regular transport neighborhoods of
-- `FinitePolyhedralComplex.exists_ball_crossingWord_eq`, in which admissible loops
-- have trivial words.


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
  choose r hr hlocal using fun z => C.exists_ball_crossingWord_loop_eq_one ν hν (hreg z)
  rw [← Subgroup.mem_bot]
  exact C.crossingWord_boundary_mem_of_cover ν hν ⊥ x e₁ e₂ f hf₁ hf₂
    (fun z => Metric.ball (f z) (r z)) (fun _ => Metric.isOpen_ball)
    (fun z => ⟨z, Metric.mem_ball_self (hr z)⟩)
    fun z y p hp => Subgroup.mem_bot.mpr (hlocal z y p hp)

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
  have hreg' (u : V) (hu : u ∈ convexHull ℝ {y.val, z.val, w.val}) :
      u ∉ singularSupport (fun P : C.walls => (P : Set V)) :=
    Set.disjoint_left.mp hreg hu
  choose r hr hlocal using fun u : convexHull ℝ {y.val, z.val, w.val} =>
    C.exists_ball_crossingWord_loop_eq_one ν hν (hreg' u.val u.property)
  have hmem := C.crossingWord_triangle_mem_of_cover ν hν ⊥ e g (Quiver.reverse d)
    (fun u => Metric.ball u.val (r u)) (fun _ => Metric.isOpen_ball)
    (fun u hu => mem_iUnion.mpr ⟨⟨u, hu⟩, Metric.mem_ball_self (hr _)⟩)
    fun u a p hp => Subgroup.mem_bot.mpr (hlocal u a p hp)
  rw [Subgroup.mem_bot] at hmem
  simp only [Quiver.Path.crossingWord_cons, Quiver.Hom.toPath, Quiver.Path.crossingWord_nil,
    mul_one, C.segmentCrossingWord_reverse ν hν] at hmem
  exact (inv_mul_eq_one.mp (by simpa only [mul_assoc] using hmem)).symm

end Mei.FinitePolyhedralComplex
