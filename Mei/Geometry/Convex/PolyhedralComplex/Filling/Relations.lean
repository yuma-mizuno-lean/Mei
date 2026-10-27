/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Admissible
public import Mei.GroupTheory.Grid

/-!
# Joint relations on the boundary of a filling grid

A transverse square filling missing the higher skeleton admits an admissible
polygonal grid whose outer word is generated normally by loops in isolated
joint neighborhoods. Regular cells contribute the identity; the internal edges
cancel in the free group, with no commutativity assumptions on wall labels.
The initial corner is fixed and the other grid vertices approximate their
parameter samples arbitrarily closely.

The generators `jointNeighborhoodWords` retain the actual loops and ambient
incidence condition, so local descriptions of joint transport can be applied
to them. They do not require a choice of meridian. Comparing the perturbed
outer boundary with a prescribed original polygon is a separate step.

This combines `FinitePolyhedralComplex.exists_admissible_subordinate_filling_grid`
with `Mei.grid_boundary_mem_normalClosure`. The inverses in the boundary formula
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

/-- A transverse filling admits an arbitrarily close admissible grid whose
outer boundary word lies in the normal closure of isolated joint relations.
`row` and `col` are the crossing words along the increasing coordinate
paths. The boundary traverses the bottom, right, top and left sides in order.
The conclusion concerns the constructed grid, without assuming that the
original boundary samples are allowed vertices. -/
theorem exists_filling_grid_boundary_mem_normalClosure_jointNeighborhoodWords
    (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
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
        let row := fun b => (List.ofFn fun a : Fin n =>
          C.segmentCrossingWord ν (e₁ a b)).reverse.prod
        let col := fun a => (List.ofFn fun b : Fin n =>
          C.segmentCrossingWord ν (e₂ a b)).reverse.prod
        (col 0)⁻¹ * (row (Fin.last n))⁻¹ * col (Fin.last n) * row 0 ∈
          Subgroup.normalClosure (C.jointNeighborhoodWords ν) := by
  classical
  obtain ⟨n, t, hn, ht0, htmono, ht1, v, hv0, hvnear, e₁, e₂, hpatch⟩ :=
    C.exists_admissible_subordinate_filling_grid ν hν A f hA hnext htrans hbase hη
  refine ⟨n, t, hn, ht0, htmono, ht1, v, hv0, hvnear, e₁, e₂, ?_⟩
  dsimp only
  let K := Subgroup.normalClosure (C.jointNeighborhoodWords ν)
  let cell := fun a b : Fin n => (((e₁ a b.castSucc).toPath.cons (e₂ a.succ b)).cons
    (Quiver.reverse (e₁ a b.succ))).cons (Quiver.reverse (e₂ a.castSucc b))
  -- The local geometry discharges every actual cell relation.
  have hcell (a b : Fin n) : (cell a b).crossingWord ν ∈ K := by
    obtain ⟨θ, -, r, hr, -, hhull, hlocal⟩ := hpatch a b
    rcases hlocal with hword | ⟨J, hJ, hθ, -, hinc⟩
    · rw [hword]
      exact K.one_mem
    · apply Subgroup.subset_normalClosure
      refine ⟨J, hJ, θ, hθ, r, hr, hinc, v (a.castSucc, b.castSucc), cell a b, ?_, rfl⟩
      have hc (c : Fin 2 × Fin 2) :
          (v (⟨a.val + c.1.val, by omega⟩, ⟨b.val + c.2.val, by omega⟩)).val ∈
            Metric.ball θ r := hhull (subset_convexHull ℝ _ (mem_range_self c))
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
      intro z hz
      simp only [cell, Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath,
        List.concat_eq_append, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hz
      rcases hz with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> assumption
  -- Extend only the edge labels, by identities, to apply the unbounded grid API.
  let a : ℕ → ℕ → FreeGroup C.walls := fun b a =>
    if ha : a < n then if hb : b ≤ n then
      (C.segmentCrossingWord ν (e₁ ⟨a, ha⟩ ⟨b, by omega⟩))⁻¹ else 1 else 1
  let b : ℕ → ℕ → FreeGroup C.walls := fun b a =>
    if hb : b < n then if ha : a ≤ n then
      (C.segmentCrossingWord ν (e₂ ⟨a, by omega⟩ ⟨b, hb⟩))⁻¹ else 1 else 1
  have hle : Subgroup.normalClosure
      {g | ∃ i < n, ∃ j < n,
        g = a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹} ≤ K := by
    apply Subgroup.normalClosure_le_normal
    rintro g ⟨i, hi, j, hj, rfl⟩
    have he : a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹ =
        ((cell ⟨j, hj⟩ ⟨i, hi⟩).crossingWord ν)⁻¹ := by
      simp [a, b, Nat.le_of_lt hi, Nat.le_of_lt hj, Nat.succ_le_iff.mpr hi,
        Nat.succ_le_iff.mpr hj, hi, hj, cell, Quiver.Path.crossingWord_cons,
        C.segmentCrossingWord_reverse ν hν, Quiver.Hom.toPath,
        Quiver.Path.crossingWord_nil, mul_assoc]
    rw [he]
    exact K.inv_mem (hcell _ _)
  have hm := K.inv_mem (hle (Mei.grid_boundary_mem_normalClosure a b n n))
  -- Recover the finite rows and columns; the added identity labels are unused.
  have hrow (i : Fin (n + 1)) :
      ((List.range n).map (a i.val)).prod =
        (List.ofFn fun j : Fin n => (C.segmentCrossingWord ν (e₁ j i))⁻¹).prod := by
    rw [← List.ofFn_getElem_eq_map]
    simp only [List.length_range, List.getElem_range]
    congr 2
    funext j
    simp [a, Nat.le_of_lt_succ i.isLt]
  have hcol (j : Fin (n + 1)) :
      ((List.range n).map (b · j.val)).prod =
        (List.ofFn fun i : Fin n => (C.segmentCrossingWord ν (e₂ j i))⁻¹).prod := by
    rw [← List.ofFn_getElem_eq_map]
    simp only [List.length_range, List.getElem_range]
    congr 2
    funext i
    simp [b, Nat.le_of_lt_succ j.isLt]
  simpa only [List.prod_reverse_noncomm, List.map_ofFn, Function.comp_def, ← hrow 0,
    ← hrow (Fin.last n), ← hcol 0, ← hcol (Fin.last n), Fin.val_zero,
    Fin.val_last, mul_inv_rev, inv_inv, mul_assoc] using hm

end Mei.FinitePolyhedralComplex
