/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.Chain
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Vertices and reversal of paths under prefunctors

A prefunctor preserving reversal of edges also preserves reversal of paths.
This extends Mathlib's `Prefunctor.MapReverse` API to `Prefunctor.mapPath`,
so that geometric projections of polygonal paths can use the same reversal law.
A prefunctor also applies its object map to the vertex list, allowing geometric
paths to be compared after forgetting some of their admissibility conditions.
Relations between consecutive vertices can be checked separately on each part
of a concatenation, using Mathlib's `List.isChain_split` at the common endpoint.
An initial segment of a vertex-and-edge sequence defines a path with its expected
length, vertex list and ordered weight. Group-valued edge weights can be gauged
at the vertices: if every gauged edge lies in a submonoid, so does the gauged
weight of the entire path. Arrow weights agreeing at matching mapped endpoints
compare paths in different quivers with the same mapped vertex list.
Additive endpoint weights also distribute over subtraction.

The sequence-path API is adapted from Codex,
[Mei PR #325](https://github.com/yuma-mizuno-lean/Mei/pull/325).
The mapped-vertex weight comparison abstracts the path induction used in
`Quiver.Path.wallCrossingSum_eq_of_cochain_eq`.
-/

public section

namespace Prefunctor

variable {U V : Type*} [Quiver U] [Quiver V]

/-- A prefunctor applies its object map to every vertex of a path. -/
@[simp]
theorem vertices_mapPath (F : U ⥤q V) {x y : U} (p : Quiver.Path x y) :
    (F.mapPath p).vertices = p.vertices.map F.obj := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

variable {U V : Type*} [Quiver U] [Quiver V]
  [Quiver.HasReverse U] [Quiver.HasReverse V]

/-- A prefunctor preserving edge reversal preserves reversal of entire paths. -/
@[simp]
theorem mapPath_reverse (F : U ⥤q V) [F.MapReverse] {x y : U} (p : Quiver.Path x y) :
    F.mapPath p.reverse = (F.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Quiver.Path.reverse, mapPath_comp, mapPath_toPath, mapPath_cons, ih,
      map_reverse]

end Prefunctor

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-- Paths with the same mapped vertex list have equal weights if their arrow
weights agree whenever the mapped endpoints agree. Neither compatibility of the
arrows nor injectivity of the vertex maps is required. -/
@[to_additive addWeight_eq_of_map_vertices_eq
/-- Paths with the same mapped vertex list have equal additive
weights if their arrow weights agree whenever the mapped endpoints agree.
Neither compatibility of the arrows nor injectivity of the vertex maps is required. -/]
theorem weight_eq_of_map_vertices_eq
    {U W M : Type*} [Quiver U] [Monoid M]
    {x y : V} {x' y' : U} (p : Path x y) (q : Path x' y')
    (f : V → W) (g : U → W)
    (w : ∀ {a b : V}, (a ⟶ b) → M) (w' : ∀ {a b : U}, (a ⟶ b) → M)
    (hw : ∀ {a b : V} {a' b' : U} (e : a ⟶ b) (e' : a' ⟶ b'),
      f a = g a' → f b = g b' → w e = w' e')
    (hpq : p.vertices.map f = q.vertices.map g) : p.weight w = q.weight w' := by
  induction p generalizing x' y' with
  | nil =>
    cases q with
    | nil => simp only [weight_nil]
    | cons q e =>
      have he := congrArg List.length hpq
      simp only [List.length_map, vertices_length, length_nil, length_cons] at he
      omega
  | @cons z t p e ih =>
    cases q with
    | nil =>
      have he := congrArg List.length hpq
      simp only [List.length_map, vertices_length, length_nil, length_cons] at he
      omega
    | @cons z' t' q e' =>
      simp only [vertices_cons, List.map_concat, List.concat_inj] at hpq
      have hz : f z = g z' := by
        have he := congrArg List.getLast? hpq.1
        simpa [List.getLast?_eq_some_getLast, p.vertices_ne_nil, q.vertices_ne_nil] using he
      rw [weight_cons, weight_cons, ih q hpq.1, hw e e' hz hpq.2]

/-- Endpoint weights depend only on the mapped vertex list, even for paths in
different quivers. No compatibility of the arrows or injectivity of the vertex
maps is required. -/
theorem addWeightOfEPs_eq_of_map_vertices_eq
    {U W E : Type*} [Quiver U] [AddMonoid E]
    {x y : V} {x' y' : U} (p : Path x y) (q : Path x' y')
    (f : V → W) (g : U → W) (w : W → W → E)
    (hpq : p.vertices.map f = q.vertices.map g) :
    p.addWeightOfEPs (fun a b => w (f a) (f b)) =
      q.addWeightOfEPs (fun a b => w (g a) (g b)) := by
  unfold addWeightOfEPs
  exact p.addWeight_eq_of_map_vertices_eq q f g _ _
    (fun _ _ ha hb => by simp only [ha, hb]) hpq

/-- Additive endpoint weights distribute over subtraction. -/
@[simp]
theorem addWeightOfEPs_sub {E : Type*} [AddCommGroup E]
    {x y : V} (p : Path x y) (w w' : V → V → E) :
    p.addWeightOfEPs (fun a b => w a b - w' a b) =
      p.addWeightOfEPs w - p.addWeightOfEPs w' := by
  induction p with
  | nil => simp only [addWeightOfEPs_nil, sub_self]
  | cons p e ih =>
    simp only [addWeightOfEPs_cons, ih]
    exact sub_add_sub_comm _ _ _ _

/-- The path formed by the first `n` successive edges of a vertex sequence. -/
def ofSeq (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1)) : (n : ℕ) → Path (x 0) (x n)
  | 0 => .nil
  | n + 1 => (ofSeq x e n).cons (e n)

@[simp]
theorem ofSeq_zero (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1)) :
    ofSeq x e 0 = .nil := (rfl)

@[simp]
theorem ofSeq_succ (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1)) (n : ℕ) :
    ofSeq x e (n + 1) = (ofSeq x e n).cons (e n) := (rfl)

@[simp]
theorem length_ofSeq (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1)) (n : ℕ) :
    (ofSeq x e n).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

/-- The vertex list of the initial sequence path, including both endpoints. -/
@[simp]
theorem vertices_ofSeq (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1)) (n : ℕ) :
    (ofSeq x e n).vertices = (List.range (n + 1)).map x := by
  induction n with
  | zero => simp
  | succ n ih => simp [vertices_cons, ih, List.range_succ]

/-- The weight of an initial sequence path is the ordered product of its edges. -/
@[simp]
theorem weight_ofSeq {M : Type*} [Monoid M]
    (x : ℕ → V) (e : ∀ n, x n ⟶ x (n + 1))
    (w : ∀ {u v : V}, (u ⟶ v) → M) (n : ℕ) :
    (ofSeq x e n).weight w = ((List.range n).map fun j => w (e j)).prod := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.prod_range_succ]

/-- A relation holds between consecutive vertices of a concatenated path exactly when
it holds along both paths. The common endpoint is counted only once. -/
theorem isChain_vertices_comp {x y z : V} (p : Path x y) (q : Path y z)
    (r : V → V → Prop) :
    (p.comp q).vertices.IsChain r ↔ p.vertices.IsChain r ∧ q.vertices.IsChain r := by
  have hq : y :: q.vertices.tail = q.vertices :=
    List.cons_head?_tail (by simp)
  rw [vertices_comp, ← hq, List.isChain_split, dropLast_append_end_eq, hq]

/-- Submonoid membership of the vertex-gauged edge weights propagates along a
path: consecutive vertex factors cancel. -/
theorem mul_weight_mul_inv_mem_of_isChain {G : Type*} [Group G]
    {x y : V} (p : Path x y)
    (K : Submonoid G) (w : ∀ {u v : V}, (u ⟶ v) → G) (t : V → G)
    (hp : p.vertices.IsChain (fun u v => ∀ e : u ⟶ v, t u * w e * (t v)⁻¹ ∈ K)) :
    t x * p.weight w * (t y)⁻¹ ∈ K := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [← comp_toPath_eq_cons, isChain_vertices_comp] at hp
    have he := (List.isChain_pair.mp hp.2) e
    simpa only [weight_cons, end_cons, mul_assoc, inv_mul_cancel_left] using
      K.mul_mem (ih hp.1) he

variable {V : Type*} [Quiver V] [Quiver.HasReverse V]

/-- Reversing a path reverses its entire vertex list. -/
@[simp]
theorem vertices_reverse {x y : V} (p : Path x y) :
    p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => simp
  | cons p e ih => simp [Path.reverse, ih]

end Quiver.Path
