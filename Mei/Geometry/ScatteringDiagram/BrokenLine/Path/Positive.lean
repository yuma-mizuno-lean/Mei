/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Positive varying-chamber decorated-ray evaluations

Choose an additive submonoid of positive coefficients for each homogeneous degree of
each chamber module. If every component transfer preserves these submonoids on the
pairs of degrees with the prescribed crossing sign and preserved normal velocity, then
every surviving whole history is positive, and every homogeneous component of the
finite weighted evaluation of a path inventory is positive. Geometric admissibility
only selects histories; it cannot introduce negative coefficients. Coincident paths
with different histories retain their multiplicities, and no endpoint genericity or
noncancellation assumption is used.

For the positivity argument by whole homogeneous decorations, see
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definition 3.1 and Theorem 1.13 (arXiv:1411.1394v2).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (Pos : ∀ q, ι q → AddSubmonoid (M q))
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀) (hx : (x : M a) ∈ Pos a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (hT : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), ν e (v c j) = ν e (v b i) →
    SignType.sign (ν e (v c j)) = ε e → ∀ y : M b, y ∈ ℳ b i → y ∈ Pos b i →
      (DirectSum.decompose (ℳ c) (T e y) j : M c) ∈ Pos c j)

include hx hT

/-- Every surviving whole history is positive in its terminal degree. -/
theorem homogeneousHistory_mem_pos_of_mem_pathDecoratedHistorySupport :
    ∀ {b : Q} (p : Path a b) (d : p.Degrees ι),
      d ∈ pathDecoratedHistorySupport T ℳ i₀ x v ν ε p →
        p.homogeneousHistory T ℳ d x ∈ Pos b (Path.Degrees.terminalDegree i₀ p d)
  | _, .nil, d, _ => by
    rw [Path.homogeneousHistory_nil, LinearMap.id_apply, Path.Degrees.terminalDegree_nil]
    exact hx
  | _, .cons p e, di, hd => by
    obtain ⟨d, i⟩ := di
    obtain ⟨hd, -, hnormal, hsign⟩ :=
      (mem_pathDecoratedHistorySupport_cons T ℳ i₀ x v ν ε p e d i).mp hd
    rw [Path.homogeneousHistory_cons_apply, Path.Degrees.terminalDegree_cons]
    exact hT e _ i hnormal hsign _ (p.homogeneousHistory_mem_vertex (T := T) (ℳ := ℳ) d i₀ x
      x.property) (homogeneousHistory_mem_pos_of_mem_pathDecoratedHistorySupport p d hd)

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)
  (s : Finset (Path a b)) (X : V)

/-- Every homogeneous component of the weighted evaluation of a path inventory is
positive. The sum runs over actual admissible rays, with their full avoidance and source
conditions, rather than over all syntactically possible histories. -/
theorem pathDecoratedEvaluation_component_mem_addSubmonoid (q : ι b) :
    (DirectSum.decompose (ℳ b) (pathDecoratedEvaluation T ℳ i₀ x s v ν ε c P W S C X) q :
      M b) ∈ Pos b q := by
  classical
  let := Fintype.ofFinite (Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X)
  rw [pathDecoratedEvaluation_def]
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  refine (Pos b q).sum_mem fun r _ => ?_
  have hmem := r.2.decoration_mem
  have hpos : r.2.decoration ∈ Pos b (Path.Degrees.terminalDegree i₀ r.1.val r.2.1.val) := by
    rw [PathDecoratedRay.decoration_def]
    exact homogeneousHistory_mem_pos_of_mem_pathDecoratedHistorySupport T ℳ Pos i₀ x hx v ν ε hT
      r.1.val r.2.1.val r.2.1.property
  by_cases hq : Path.Degrees.terminalDegree i₀ r.1.val r.2.1.val = q
  · subst hq
    rwa [DirectSum.decompose_of_mem_same _ hmem]
  · rw [DirectSum.decompose_of_mem_ne _ hmem hq]
    exact (Pos b q).zero_mem

end Mei
