/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Grid
import Mei.Geometry.Convex.Polyhedron.GraphPerturbation

/-!
# Admissible grids subordinate to local crossing relations

A transverse square filling avoiding the higher skeleton admits a finite grid
of actual admissible horizontal and vertical segments. Its initial corner stays
fixed, and all other vertices can be moved arbitrarily little. Each original
parameter patch and the convex hull of its new corners lie in one common ball.
The cell loop either has trivial crossing word or lies in a ball incident only
to cells containing one joint, isolated in the original filling slice.

This supplies admissible edges for decomposing a filled loop into local relations.
It does not identify the words in joint balls with meridians. The new vertices
need not stay in the original affine slice; the incidence conclusion in joint
balls holds in the entire ambient space.

The construction combines `FinitePolyhedralComplex.exists_subordinate_filling_grid`
with `Convex.exists_admissible_graph_perturbation`. The former supplies a uniform
perturbation margin for all patches; the latter chooses all shared vertices at
once, so adjacent cell loops use exactly the same edges with opposite directions.
-/

public section

noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Construct admissible grid edges subordinate to regular or isolating joint
balls. The allowed initial corner is fixed and the other vertices move by less
than any prescribed positive tolerance. Regular cell loops have trivial word;
joint cells retain both ambient incidence control and isolation in the original
slice. No embeddedness, injectivity or nondegeneracy is required of the filling. -/
theorem exists_admissible_subordinate_filling_grid (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (A : AffineSubspace ℝ V) (f : C(↥unitInterval × ↥unitInterval, V))
    (hA : range f ⊆ A)
    (hnext : Disjoint (range f) (C.codimensionAtLeast 3).support)
    (htrans : ∀ J ∈ C.joints, (range f ∩ J).Nonempty →
      Disjoint A.direction (affineSpan ℝ J).direction)
    (hbase : ∀ P : C.walls, f (0, 0) ∉ (P : Set V))
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      ∃ v : Fin (n + 1) × Fin (n + 1) →
        WallComplement (fun P : C.walls => (P : Set V)),
        (v (0, 0)).val = f (0, 0) ∧
        (∀ c, dist (v c).val (f (t c.1, t c.2)) < η) ∧
      ∃ (e₁ : ∀ (a : Fin n) (b : Fin (n + 1)),
          v (a.castSucc, b) ⟶ v (a.succ, b))
        (e₂ : ∀ (a : Fin (n + 1)) (b : Fin n),
          v (a, b.castSucc) ⟶ v (a, b.succ)),
      ∀ a b : Fin n, ∃ θ ∈ range f, ∃ r > 0,
        MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (Metric.ball θ r) ∧
        convexHull ℝ (range (fun c : Fin 2 × Fin 2 =>
          (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val)) ⊆
            Metric.ball θ r ∧
        (((((e₁ a b.castSucc).toPath.cons (e₂ a.succ b)).cons
            (Quiver.reverse (e₁ a b.succ))).cons
            (Quiver.reverse (e₂ a.castSucc b))).crossingWord ν = 1 ∨
          ∃ J ∈ C.joints, θ ∈ intrinsicInterior ℝ J ∧
            Metric.ball θ r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {θ} ∧
            ∀ Q ∈ C.cells, (Metric.ball θ r ∩ Q).Nonempty → J ⊆ Q) := by
  classical
  have := h.finiteDimensional
  obtain ⟨n, t, hn, ht0, htmono, ht1, ε, hε, hpatch⟩ :=
    C.exists_subordinate_filling_grid ν hν A f hA hnext htrans
  let z : Fin (n + 1) × Fin (n + 1) → V := fun c => f (t c.1, t c.2)
  -- Both coordinate directions belong to one finite graph. Choosing its
  -- vertices simultaneously makes the edges shared between neighboring cells.
  let edge : (Fin (n + 1) × Fin (n + 1)) →
      (Fin (n + 1) × Fin (n + 1)) → Prop := fun c d =>
    (d.1.val = c.1.val + 1 ∧ d.2 = c.2) ∨
      (d.1 = c.1 ∧ d.2.val = c.2.val + 1)
  obtain ⟨w, hw0, hwnear, hwallowed, hwedge⟩ :=
    exists_admissible_graph_perturbation (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      z edge {(0, 0)}
      (by
        intro c hc P
        simpa only [Finset.mem_singleton.mp hc, z, Fin.val_zero, ht0] using hbase P)
      (by
        intro c hc d hd hcd
        have hc0 := Finset.mem_singleton.mp hc
        have hd0 := Finset.mem_singleton.mp hd
        simp [edge, hc0, hd0] at hcd)
      (fun _ => min ε η) (fun _ => lt_min hε hη)
  let v : Fin (n + 1) × Fin (n + 1) →
      WallComplement (fun P : C.walls => (P : Set V)) :=
    fun c => ⟨w c, hwallowed c⟩
  have hedge (c d) (hcd : edge c d) : Nonempty (v c ⟶ v d) :=
    ⟨PLift.up ((mem_admissiblePairs_iff (v c) (v d)).mp (hwedge c d hcd))⟩
  let e₁ := fun (a : Fin n) (b : Fin (n + 1)) =>
    (hedge (a.castSucc, b) (a.succ, b) (Or.inl ⟨rfl, rfl⟩)).some
  let e₂ := fun (a : Fin (n + 1)) (b : Fin n) =>
    (hedge (a, b.castSucc) (a, b.succ) (Or.inr ⟨rfl, rfl⟩)).some
  refine ⟨n, t, hn, ht0, htmono, ht1, v, ?_, ?_, e₁, e₂, fun a b => ?_⟩
  · simpa only [v, z, Fin.val_zero, ht0] using hw0 (0, 0) (Finset.mem_singleton_self _)
  · intro c
    exact (hwnear c).trans_le (min_le_right _ _)
  · obtain ⟨θ, hθ, r, hr, hcover, hhull, hlocal⟩ := hpatch a b
    have hh : convexHull ℝ (range (fun c : Fin 2 × Fin 2 =>
        (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val)) ⊆
          Metric.ball θ r :=
      hhull _ (fun c => (hwnear _).trans_le (min_le_left _ _))
    refine ⟨θ, hθ, r, hr, hcover, hh, ?_⟩
    rcases hlocal with hword | hjoint
    · left
      -- All four vertices, hence all four affine edges, lie in the regular ball.
      have hc (c : Fin 2 × Fin 2) :
          (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val ∈
            Metric.ball θ r := hh (subset_convexHull ℝ _ (mem_range_self c))
      have h00 : (v (a.castSucc, b.castSucc)).val ∈ Metric.ball θ r := by
        convert hc (0, 0) using 2
        congr 2
      have h10 : (v (a.succ, b.castSucc)).val ∈ Metric.ball θ r := by
        convert hc (1, 0) using 2
        congr 2
      have h11 : (v (a.succ, b.succ)).val ∈ Metric.ball θ r := by
        convert hc (1, 1) using 2
        congr 2
      have h01 : (v (a.castSucc, b.succ)).val ∈ Metric.ball θ r := by
        convert hc (0, 1) using 2
        congr 2
      exact (hword _ _ _ Quiver.Path.nil
        (by
          intro u hu
          simp only [Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath,
            List.concat_eq_append, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hu
          rcases hu with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> assumption)
        (by simpa only [Quiver.Path.vertices_nil, List.mem_singleton] using
          fun u (hu : u = v (a.castSucc, b.castSucc)) => hu ▸ h00)).trans
        (Quiver.Path.crossingWord_nil ν)
    · exact Or.inr hjoint

end Mei.FinitePolyhedralComplex
