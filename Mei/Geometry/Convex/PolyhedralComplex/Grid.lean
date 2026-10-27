/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.GroupTheory.Grid
public import Mei.Geometry.Convex.Polyhedron.GraphPerturbation

/-!
# Crossing words under rectangular subdivision

For a rectangular grid of admissible segments, the word around the outer
boundary lies in the normal closure of the words around its cells. Interior
edges cancel with their reverses without requiring commutative wall labels.
This permits a subdivided filling to be reduced to its local boundary relations.

The construction uses `Mei.grid_boundary_mem_normalClosure`, the reversal law
for crossing words, and `Convex.exists_admissible_graph_perturbation`. Invert each
edge word, take the increasing-order product, and then invert the entire product
to obtain the crossing word with the first crossing as the rightmost factor.
Admissible grid perturbations also retain a prescribed initial corner.
No geometric filling or local consistency condition is assumed by this
combinatorial subdivision result.

The crossing-word grid argument is adapted from Codex,
[Mei PR #325](https://github.com/yuma-mizuno-lean/Mei/pull/325).
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Perturb a finite rectangular grid to have admissible edges, fixing its
allowed initial corner and moving every vertex by less than the given tolerance.
The original grid may be degenerate or self-overlapping. -/
theorem exists_admissible_grid_perturbation (C : FinitePolyhedralComplex h)
    {m n : ℕ} (z : Fin (m + 1) × Fin (n + 1) → V)
    (hbase : ∀ P : C.walls, z (0, 0) ∉ (P : Set V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin (m + 1) × Fin (n + 1) →
        WallComplement (fun P : C.walls => (P : Set V)),
      (v (0, 0)).val = z (0, 0) ∧ (∀ c, dist (v c).val (z c) < ε) ∧
      Nonempty (∀ (a : Fin m) (b : Fin (n + 1)),
        v (a.castSucc, b) ⟶ v (a.succ, b)) ∧
      Nonempty (∀ (a : Fin (m + 1)) (b : Fin n),
        v (a, b.castSucc) ⟶ v (a, b.succ)) := by
  classical
  have := h.finiteDimensional
  -- Both coordinate directions belong to one finite graph. Choosing its
  -- vertices simultaneously makes the edges shared between neighboring cells.
  let edge : (Fin (m + 1) × Fin (n + 1)) →
      (Fin (m + 1) × Fin (n + 1)) → Prop := fun c d =>
    (d.1.val = c.1.val + 1 ∧ d.2 = c.2) ∨
      (d.1 = c.1 ∧ d.2.val = c.2.val + 1)
  obtain ⟨w, hw0, hwnear, hwallowed, hwedge⟩ :=
    exists_admissible_graph_perturbation (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      z edge {(0, 0)}
      (by
        intro c hc P
        simpa only [Finset.mem_singleton.mp hc] using hbase P)
      (by
        intro c hc d hd hcd
        have hc0 := Finset.mem_singleton.mp hc
        have hd0 := Finset.mem_singleton.mp hd
        simp [edge, hc0, hd0] at hcd)
      (fun _ => ε) (fun _ => hε)
  let v : Fin (m + 1) × Fin (n + 1) →
      WallComplement (fun P : C.walls => (P : Set V)) :=
    fun c => ⟨w c, hwallowed c⟩
  have hedge (c d) (hcd : edge c d) : Nonempty (v c ⟶ v d) :=
    ⟨PLift.up ((mem_admissiblePairs_iff (v c) (v d)).mp (hwedge c d hcd))⟩
  let e₁ := fun (a : Fin m) (b : Fin (n + 1)) =>
    (hedge (a.castSucc, b) (a.succ, b) (Or.inl ⟨rfl, rfl⟩)).some
  let e₂ := fun (a : Fin (m + 1)) (b : Fin n) =>
    (hedge (a, b.castSucc) (a, b.succ) (Or.inr ⟨rfl, rfl⟩)).some
  exact ⟨v, hw0 (0, 0) (Finset.mem_singleton_self _), hwnear, ⟨e₁⟩, ⟨e₂⟩⟩

/-- The actual outer crossing word of an admissible rectangular grid is generated
normally by its actual four-edge cell words. The geometry may be degenerate or
self-overlapping, and empty rows and columns are allowed. -/
theorem crossingWord_grid_boundary_mem_normalClosure (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    {m n : ℕ} (v : Fin (m + 1) × Fin (n + 1) →
      WallComplement (fun P : C.walls => (P : Set V)))
    (e₁ : ∀ (a : Fin m) (b : Fin (n + 1)), v (a.castSucc, b) ⟶ v (a.succ, b))
    (e₂ : ∀ (a : Fin (m + 1)) (b : Fin n), v (a, b.castSucc) ⟶ v (a, b.succ)) :
    let row := fun b => (List.ofFn fun a : Fin m =>
      C.segmentCrossingWord ν (e₁ a b)).reverse.prod
    let col := fun a => (List.ofFn fun b : Fin n =>
      C.segmentCrossingWord ν (e₂ a b)).reverse.prod
    let cell := fun a b => (((e₁ a b.castSucc).toPath.cons (e₂ a.succ b)).cons
      (Quiver.reverse (e₁ a b.succ))).cons (Quiver.reverse (e₂ a.castSucc b))
    (col 0)⁻¹ * (row (Fin.last n))⁻¹ * col (Fin.last m) * row 0 ∈
      Subgroup.normalClosure {g | ∃ a b, g = (cell a b).crossingWord ν} := by
  classical
  dsimp only
  let cell := fun a b => (((e₁ a b.castSucc).toPath.cons (e₂ a.succ b)).cons
    (Quiver.reverse (e₁ a b.succ))).cons (Quiver.reverse (e₂ a.castSucc b))
  let K := Subgroup.normalClosure {g | ∃ a b, g = (cell a b).crossingWord ν}
  have hcell a b : (cell a b).crossingWord ν ∈ K :=
    Subgroup.subset_normalClosure ⟨a, b, rfl⟩
  -- Extend only the edge labels to use the algebraic grid theorem.
  let a : ℕ → ℕ → FreeGroup C.walls := fun b a =>
    if ha : a < m then if hb : b ≤ n then
      (C.segmentCrossingWord ν (e₁ ⟨a, ha⟩ ⟨b, by omega⟩))⁻¹ else 1 else 1
  let b : ℕ → ℕ → FreeGroup C.walls := fun b a =>
    if hb : b < n then if ha : a ≤ m then
      (C.segmentCrossingWord ν (e₂ ⟨a, by omega⟩ ⟨b, hb⟩))⁻¹ else 1 else 1
  have hle : Subgroup.normalClosure
      {g | ∃ i < n, ∃ j < m,
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
  have hm := K.inv_mem (hle (Mei.grid_boundary_mem_normalClosure a b n m))
  -- Recover the finite rows and columns; the added identity labels are unused.
  have hrow (i : Fin (n + 1)) :
      ((List.range m).map (a i.val)).prod =
        (List.ofFn fun j : Fin m => (C.segmentCrossingWord ν (e₁ j i))⁻¹).prod := by
    rw [← List.ofFn_getElem_eq_map]
    simp only [List.length_range, List.getElem_range]
    congr 2
    funext j
    simp [a, Nat.le_of_lt_succ i.isLt]
  have hcol (j : Fin (m + 1)) :
      ((List.range n).map (b · j.val)).prod =
        (List.ofFn fun i : Fin n => (C.segmentCrossingWord ν (e₂ j i))⁻¹).prod := by
    rw [← List.ofFn_getElem_eq_map]
    simp only [List.length_range, List.getElem_range]
    congr 2
    funext i
    simp [b, Nat.le_of_lt_succ j.isLt]
  simpa only [List.prod_reverse_noncomm, List.map_ofFn, Function.comp_def, ← hrow 0,
    ← hrow (Fin.last n), ← hcol 0, ← hcol (Fin.last m), Fin.val_zero,
    Fin.val_last, mul_inv_rev, inv_inv, mul_assoc] using hm

end Mei.FinitePolyhedralComplex
