/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Grid
public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport
public import Mei.Topology.ContinuousMap.Subdivision

/-!
# Joint relations on the boundary of a filling grid

A continuous square filling missing the higher skeleton admits an admissible
polygonal grid whose outer word is generated normally by loops in
joint neighborhoods. Regular cells contribute the identity; the internal edges
cancel in the free group, with no commutativity assumptions on wall labels.
The initial corner is fixed and the other grid vertices approximate their
parameter samples arbitrarily closely.

The generators `jointNeighborhoodWords` retain the actual loops and ambient
incidence condition, so local descriptions of joint transport can be applied
to them. They do not require a choice of meridian. Comparing the perturbed
outer boundary with a prescribed original polygon is a separate step.

This combines `ContinuousMap.exists_grid_subdivision_convexHull`,
`FinitePolyhedralComplex.exists_admissible_grid_perturbation`, and
`FinitePolyhedralComplex.crossingWord_grid_boundary_mem_normalClosure`.
Local balls come from `FinitePolyhedralComplex.exists_isolating_ball` and
`FinitePolyhedralComplex.exists_ball_crossingWord_eq`. The inverses in the boundary formula
implement the convention that the first crossing acts on the right.
-/

public section

noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Words of loops contained in balls centered in a joint's relative interior,
where every cell meeting the ball contains that joint. -/
def jointNeighborhoodWords (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) : Set (FreeGroup C.walls) :=
  {g | ∃ J ∈ C.joints, ∃ θ ∈ intrinsicInterior ℝ J, ∃ r > 0,
    (∀ Q ∈ C.cells, (Metric.ball θ r ∩ Q).Nonempty → J ⊆ Q) ∧
    ∃ (x : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath x x),
      (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ r) ∧ g = p.crossingWord ν}

/-- Membership records an actual local loop and control of every incident cell. -/
@[simp]
theorem mem_jointNeighborhoodWords (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) (g : FreeGroup C.walls) :
    g ∈ C.jointNeighborhoodWords ν ↔
      ∃ J ∈ C.joints, ∃ θ ∈ intrinsicInterior ℝ J, ∃ r > 0,
        (∀ Q ∈ C.cells, (Metric.ball θ r ∩ Q).Nonempty → J ⊆ Q) ∧
        ∃ (x : WallComplement (fun P : C.walls => (P : Set V)))
          (p : AdmissiblePLPath x x),
          (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ r) ∧ g = p.crossingWord ν := Iff.rfl

/-- A continuous filling missing the higher skeleton admits an arbitrarily close
admissible grid whose outer boundary word lies in the normal closure of
joint-neighborhood relations.
`row` and `col` are the crossing words along the increasing coordinate
paths. The boundary traverses the bottom, right, top and left sides in order.
The conclusion concerns the constructed grid, without assuming that the
original boundary samples are allowed vertices. -/
theorem exists_filling_grid_boundary_mem_normalClosure_jointNeighborhoodWords
    (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (f : C(↥unitInterval × ↥unitInterval, V))
    (hnext : Disjoint (range f) (C.codimensionAtLeast 3).support)
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
        let row := fun b => (List.ofFn fun a : Fin n =>
          C.segmentCrossingWord ν (e₁ a b)).reverse.prod
        let col := fun a => (List.ofFn fun b : Fin n =>
          C.segmentCrossingWord ν (e₂ a b)).reverse.prod
        (col 0)⁻¹ * (row (Fin.last n))⁻¹ * col (Fin.last n) * row 0 ∈
          Subgroup.normalClosure (C.jointNeighborhoodWords ν) := by
  classical
  -- Incidence neighborhoods need no transverse slice or isolated joint encounter.
  have hlocal (θ : range f) : ∃ r > 0,
      (∀ (x y : WallComplement (fun P : C.walls => (P : Set V)))
        (p q : AdmissiblePLPath x y),
        (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ.val r) →
        (∀ z ∈ q.vertices, z.val ∈ Metric.ball θ.val r) →
          p.crossingWord ν = q.crossingWord ν) ∨
      ∃ J ∈ C.joints, θ.val ∈ intrinsicInterior ℝ J ∧
        ∀ Q ∈ C.cells, (Metric.ball θ.val r ∩ Q).Nonempty → J ⊆ Q := by
    by_cases hθ : θ.val ∈ (C.codimensionAtLeast 2).support
    · obtain ⟨J, hJ, _⟩ := C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hθ
        (hnext.notMem_of_mem_left θ.property)
      obtain ⟨r, hr, -, -, -, hinc⟩ := C.exists_isolating_ball hJ.1 hJ.2
      exact ⟨r, hr, Or.inr ⟨J, hJ.1, hJ.2, hinc⟩⟩
    · obtain ⟨r, hr, hword⟩ := C.exists_ball_crossingWord_eq ν hν
        (fun hs => hθ (C.singularSupport_walls_subset_support_codimensionAtLeast hs))
      exact ⟨r, hr, Or.inl hword⟩
  choose r hr hmodel using hlocal
  obtain ⟨n, t, hn, ht0, htmono, ht1, -, ε, hε, hpatch⟩ :=
    f.exists_grid_subdivision_convexHull
      (fun θ : range f => Metric.ball θ.val (r θ)) (fun _ => Metric.isOpen_ball)
      (fun x => ⟨⟨f x, mem_range_self x⟩, Metric.mem_ball_self (hr _)⟩)
      ∅ countable_empty (notMem_empty _) (notMem_empty _)
  obtain ⟨v, hv0, hvnear, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    C.exists_admissible_grid_perturbation (fun c : Fin (n + 1) × Fin (n + 1) =>
      f (t c.1, t c.2)) (by simpa only [Fin.val_zero, ht0] using hbase) (lt_min hε hη)
  refine ⟨n, t, hn, ht0, htmono, ht1, v, ?_, ?_, e₁, e₂, ?_⟩
  · simpa only [Fin.val_zero, ht0] using hv0
  · exact fun c => (hvnear c).trans_le (min_le_right _ _)
  dsimp only
  let K := Subgroup.normalClosure (C.jointNeighborhoodWords ν)
  let cell := fun a b : Fin n => (((e₁ a b.castSucc).toPath.cons (e₂ a.succ b)).cons
    (Quiver.reverse (e₁ a b.succ))).cons (Quiver.reverse (e₂ a.castSucc b))
  -- The local geometry discharges every actual cell relation.
  have hcell (a b : Fin n) : (cell a b).crossingWord ν ∈ K := by
    obtain ⟨θ, -, hhull⟩ := hpatch a b
    have hh := hhull (fun c : Fin 2 × Fin 2 =>
      (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val)
      (fun c => (hvnear _).trans_le (min_le_left _ _))
    have hvertices : ∀ z ∈ (cell a b).vertices, z.val ∈ Metric.ball θ.val (r θ) := by
      intro z hz
      obtain ⟨c, hc⟩ := Quiver.Path.grid_cell_vertices_subset_range v e₁ e₂ a b z hz
      exact hh (subset_convexHull ℝ _ ⟨c, congrArg WallComplement.val hc⟩)
    rcases hmodel θ with hword | ⟨J, hJ, hθ, hinc⟩
    · have heq := hword _ _ (cell a b) Quiver.Path.nil hvertices
        (by simpa only [Quiver.Path.vertices_nil, List.mem_singleton] using
          fun z (hz : z = v (a.castSucc, b.castSucc)) => hz ▸
            hvertices _ (cell a b).start_mem_vertices)
      rw [heq, Quiver.Path.crossingWord_nil]
      exact K.one_mem
    · exact Subgroup.subset_normalClosure
        ⟨J, hJ, θ.val, hθ, r θ, hr θ, hinc, v (a.castSucc, b.castSucc),
          cell a b, hvertices, rfl⟩
  have hle : Subgroup.normalClosure {g | ∃ a b, g = (cell a b).crossingWord ν} ≤ K :=
    Subgroup.normalClosure_le_normal (by
      rintro g ⟨a, b, rfl⟩
      exact hcell a b)
  exact hle (C.crossingWord_grid_boundary_mem_normalClosure ν hν v e₁ e₂)

end Mei.FinitePolyhedralComplex
