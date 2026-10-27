/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Mesh
public import Mei.Geometry.Convex.Polyhedron.Filling

/-!
# Subordinate admissible grids retaining the boundary

A joint-transverse square filling with affine admissible sides admits a grid
whose boundary vertices remain exactly on those sides. Each original parameter
patch and the convex hull of its new corners lie in the same regular or isolating
joint ball. Thus subdividing the filling retains its original boundary geometry,
even when a uniform mesh would place a boundary vertex on a wall.

The construction uses `Convex.exists_admissible_filling_grid_fixed_boundary`
with the local models of
`FinitePolyhedralComplex.exists_ball_crossingWord_eq_or_isolating_joint`.
The regular alternative gives path independence for admissible paths with fixed endpoints
in the ball; the joint alternative controls ambient cell incidence as
well as isolation in the original affine slice.
-/

public section

noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A transverse square with four affine admissible sides has a subordinate
admissible grid fixing every boundary vertex. In regular patches, crossing words
depend only on endpoints; joint patches isolate one joint in the original
slice and meet only ambient cells containing it. Interior vertices may move
arbitrarily little and need not remain in that slice. -/
theorem exists_admissible_filling_grid_fixed_boundary (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (x : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)))
    (e₁ : ∀ b : Fin 2, x (0, b) ⟶ x (1, b))
    (e₂ : ∀ a : Fin 2, x (a, 0) ⟶ x (a, 1))
    (A : AffineSubspace ℝ V) (f : C(↥unitInterval × ↥unitInterval, V))
    (hf₁ : ∀ (b : Fin 2) (s : unitInterval),
      f (s, if b = 0 then 0 else 1) =
        AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ))
    (hf₂ : ∀ (a : Fin 2) (s : unitInterval),
      f (if a = 0 then 0 else 1, s) =
        AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ))
    (hA : range f ⊆ A)
    (hnext : Disjoint (range f) (C.codimensionAtLeast 3).support)
    (htrans : ∀ J ∈ C.joints, (range f ∩ J).Nonempty →
      Disjoint A.direction (affineSpan ℝ J).direction)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      ∃ v : Fin (n + 1) × Fin (n + 1) →
          WallComplement (fun P : C.walls => (P : Set V)),
        (∀ c, c.1 = 0 ∨ c.1 = Fin.last n ∨ c.2 = 0 ∨ c.2 = Fin.last n →
          (v c).val = f (t c.1, t c.2)) ∧
        (∀ c, dist (v c).val (f (t c.1, t c.2)) < η) ∧
      ∃ (_ : ∀ (a : Fin n) (b : Fin (n + 1)),
          v (a.castSucc, b) ⟶ v (a.succ, b))
        (_ : ∀ (a : Fin (n + 1)) (b : Fin n),
          v (a, b.castSucc) ⟶ v (a, b.succ)),
      ∀ a b : Fin n, ∃ θ ∈ range f, ∃ r > 0,
        MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (Metric.ball θ r) ∧
        convexHull ℝ (range (fun c : Fin 2 × Fin 2 =>
          (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val)) ⊆
            Metric.ball θ r ∧
        ((∀ (y z : WallComplement (fun P : C.walls => (P : Set V)))
          (p q : AdmissiblePLPath y z),
          (∀ w ∈ p.vertices, w.val ∈ Metric.ball θ r) →
          (∀ w ∈ q.vertices, w.val ∈ Metric.ball θ r) →
            p.crossingWord ν = q.crossingWord ν) ∨
        ∃ J ∈ C.joints, θ ∈ intrinsicInterior ℝ J ∧
          Metric.ball θ r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {θ} ∧
          ∀ Q ∈ C.cells, (Metric.ball θ r ∩ Q).Nonempty → J ⊆ Q) := by
  have := h.finiteDimensional
  choose r hr hlocal using fun θ : range f =>
    C.exists_ball_crossingWord_eq_or_isolating_joint ν hν A (hA θ.property)
      (hnext.notMem_of_mem_left θ.property)
      (fun J hJ hθJ => htrans J hJ ⟨θ.val, θ.property, hθJ⟩)
  obtain ⟨n, t, hn, ht0, htmono, ht1, v, hvfix, hvnear, a₁, a₂, hgrid⟩ :=
    Mei.Convex.exists_admissible_filling_grid_fixed_boundary
      (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      x e₁ e₂ f hf₁ hf₂ (fun θ : range f => Metric.ball θ.val (r θ))
      (fun _ => Metric.isOpen_ball)
      (fun z => ⟨⟨f z, mem_range_self z⟩, Metric.mem_ball_self (hr ⟨f z, mem_range_self z⟩)⟩) hη
  refine ⟨n, t, hn, ht0, htmono, ht1, v, hvfix, hvnear, a₁, a₂, fun a b => ?_⟩
  obtain ⟨θ, hpatch, hhull⟩ := hgrid a b
  exact ⟨θ.val, θ.property, r θ, hr θ, hpatch, hhull, hlocal θ⟩

end Mei.FinitePolyhedralComplex
