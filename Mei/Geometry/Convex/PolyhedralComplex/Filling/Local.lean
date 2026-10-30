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
Suppose a continuous square with realized admissible polygonal sides is covered by open sets,
in each of which every admissible polygonal loop has crossing word in `K`. Then the boundary
word of the square lies in `K`. A filled triangle, viewed as a square with one constant side,
has the same property. Neither the square nor the triangle needs to be embedded or nondegenerate,
and their boundary paths are kept fixed.

This reduces global relations among crossing words to local ones. Regular neighbourhoods,
where crossing words are path independent, give `K = ⊥`; isolating joint neighbourhoods give
the normal closure of the joint meridians.

The proof subdivides the square by `Mei.Convex.exists_admissible_filling_grid_fixed_boundary`,
places each grid cell in one of the open sets, and combines
`FinitePolyhedralComplex.crossingWord_grid_boundary_mem_normalClosure` with
`FinitePolyhedralComplex.segmentCrossingWord_eq_prod_sampling_of_endpoints` on the four affine
sides. For realized polygonal sides,
`FinitePolyhedralComplex.crossingWord_boundary_mem_of_cover_of_realization` uses a grid passing
through their dyadic breakpoints and
`Quiver.Path.crossingWord_eq_prod_ofFn_sampling`.
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

/-- Let a continuous square whose four sides are the realizations of admissible polygonal paths
be covered by open sets in which every admissible loop has crossing word in a normal subgroup
`K`. Then the word of its boundary loop lies in `K`. The square need not be embedded, and its
sides are kept fixed. -/
theorem crossingWord_boundary_mem_of_cover_of_realization
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (K : Subgroup (FreeGroup C.walls)) [K.Normal]
    {x₀₀ x₁₀ x₀₁ x₁₁ : WallComplement (fun P : C.walls => (P : Set V))}
    (p₀ : AdmissiblePLPath x₀₀ x₁₀) (p₁ : AdmissiblePLPath x₀₁ x₁₁)
    (r₀ : AdmissiblePLPath x₀₀ x₀₁) (r₁ : AdmissiblePLPath x₁₀ x₁₁)
    (f : C(I × I, V))
    (hp₀ : ∀ s, f (s, 0) = p₀.toContinuousPath s) (hp₁ : ∀ s, f (s, 1) = p₁.toContinuousPath s)
    (hr₀ : ∀ s, f (0, s) = r₀.toContinuousPath s) (hr₁ : ∀ s, f (1, s) = r₁.toContinuousPath s)
    {κ : Type*} (U : κ → Set V) (hU : ∀ j, IsOpen (U j)) (hcover : ∀ z, ∃ j, f z ∈ U j)
    (hlocal : ∀ j (y : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath y y), (∀ w ∈ p.vertices, w.val ∈ U j) → p.crossingWord ν ∈ K) :
    ((p₀.comp r₁).comp (p₁.reverse.comp r₀.reverse)).crossingWord ν ∈ K := by
  classical
  have := h.finiteDimensional
  have hclosed (P : C.walls) : IsClosed (P : Set V) :=
    (C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property)).isClosed
  -- The dyadic breakpoints of all four sides.
  let L := p₀.length + p₁.length + r₀.length + r₁.length
  let τ : ℕ → I := fun k => ⟨1 / 2 ^ (k + 1), by positivity,
    by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)⟩
  let T : Finset I := (Finset.range L).image τ
  -- The countably many parameters at which some side meets a wall.
  let A : ∀ {a b : WallComplement (fun P : C.walls => (P : Set V))},
      AdmissiblePLPath a b → Set ℝ := fun q =>
    {s | ∃ hs : s ∈ Icc (0 : ℝ) 1, ∃ P : C.walls, q.toContinuousPath ⟨s, hs⟩ ∈ (P : Set V)}
  let S : Set ℝ := ((A p₀ ∪ A p₁) ∪ A r₀) ∪ A r₁
  have hS : S.Countable :=
    ((p₀.countable_setOf_toContinuousPath_mem.union
      p₁.countable_setOf_toContinuousPath_mem).union
      r₀.countable_setOf_toContinuousPath_mem).union r₁.countable_setOf_toContinuousPath_mem
  have hoff {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) (hq : A q ⊆ S) (s : I) (hs : (s : ℝ) ∉ S)
      (P : C.walls) : q.toContinuousPath s ∉ (P : Set V) :=
    fun hP => hs (hq ⟨s.2, P, hP⟩)
  have hsub₀ : A p₀ ⊆ S := fun _ hs => Or.inl (Or.inl (Or.inl hs))
  have hsub₁ : A p₁ ⊆ S := fun _ hs => Or.inl (Or.inl (Or.inr hs))
  have hsub₂ : A r₀ ⊆ S := fun _ hs => Or.inl (Or.inr hs)
  have hsub₃ : A r₁ ⊆ S := fun _ hs => Or.inr hs
  -- The endpoints and the dyadic breakpoints of every side are allowed.
  have hstart {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) : (0 : ℝ) ∉ A q := by
    rintro ⟨hs, P, hP⟩
    rw [Set.Icc.mk_zero, Path.source] at hP
    exact a.notMem P hP
  have hend {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) : (1 : ℝ) ∉ A q := by
    rintro ⟨hs, P, hP⟩
    rw [Set.Icc.mk_one, Path.target] at hP
    exact b.notMem P hP
  have hdyadic {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) (k : ℕ) : (τ k : ℝ) ∉ A q := by
    rintro ⟨hs, P, hP⟩
    exact q.toContinuousPath_notMem_of_eq_half_pow k (s := ⟨_, hs⟩) rfl P hP
  have h0 : (0 : ℝ) ∉ S := by
    simp only [S, mem_union, not_or]
    exact ⟨⟨⟨hstart p₀, hstart p₁⟩, hstart r₀⟩, hstart r₁⟩
  have h1 : (1 : ℝ) ∉ S := by
    simp only [S, mem_union, not_or]
    exact ⟨⟨⟨hend p₀, hend p₁⟩, hend r₀⟩, hend r₁⟩
  have hT (τ' : I) (hτ' : τ' ∈ T) : (τ' : ℝ) ∉ S := by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hτ'
    simp only [S, mem_union, not_or]
    exact ⟨⟨⟨hdyadic p₀ k, hdyadic p₁ k⟩, hdyadic r₀ k⟩, hdyadic r₁ k⟩
  have hSside (s r : I) (hr : r = 0 ∨ r = 1) (hs : (s : ℝ) ∉ S) (P : C.walls) :
      f (s, r) ∉ (P : Set V) ∧ f (r, s) ∉ (P : Set V) := by
    rcases hr with rfl | rfl
    · rw [hp₀, hr₀]
      exact ⟨hoff p₀ hsub₀ s hs P, hoff r₀ hsub₂ s hs P⟩
    · rw [hp₁, hr₁]
      exact ⟨hoff p₁ hsub₁ s hs P, hoff r₁ hsub₃ s hs P⟩
  -- Between unseparated allowed parameters, each side is an admissible segment.
  have hpair {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) (hq : q.length ≤ L) (hqS : A q ⊆ S)
      {s₁ s₂ : I} (h₁₂ : s₁ ≤ s₂) (hs₁ : (s₁ : ℝ) ∉ S) (hs₂ : (s₂ : ℝ) ∉ S)
      (hsep : ∀ τ' ∈ T, τ' ≤ s₁ ∨ s₂ ≤ τ') :
      (q.toContinuousPath s₁, q.toContinuousPath s₂) ∈
        admissiblePairs (fun P : C.walls => (P : Set V)) :=
    q.toContinuousPath_mem_admissiblePairs hclosed hq h₁₂
      (fun k hk => hsep (τ k) (Finset.mem_image_of_mem τ (Finset.mem_range.mpr hk)))
      (hoff q hqS s₁ hs₁) (hoff q hqS s₂ hs₂)
  have hside (s₁ s₂ r : I) (hr : r = 0 ∨ r = 1) (h₁₂ : s₁ ≤ s₂) (hs₁ : (s₁ : ℝ) ∉ S)
      (hs₂ : (s₂ : ℝ) ∉ S) (hsep : ∀ τ' ∈ T, τ' ≤ s₁ ∨ s₂ ≤ τ') :
      (f (s₁, r), f (s₂, r)) ∈ admissiblePairs (fun P : C.walls => (P : Set V)) ∧
        (f (r, s₁), f (r, s₂)) ∈ admissiblePairs (fun P : C.walls => (P : Set V)) := by
    rcases hr with rfl | rfl
    · rw [hp₀, hp₀, hr₀, hr₀]
      exact ⟨hpair p₀ (by omega) hsub₀ h₁₂ hs₁ hs₂ hsep,
        hpair r₀ (by omega) hsub₂ h₁₂ hs₁ hs₂ hsep⟩
    · rw [hp₁, hp₁, hr₁, hr₁]
      exact ⟨hpair p₁ (by omega) hsub₁ h₁₂ hs₁ hs₂ hsep,
        hpair r₁ (by omega) hsub₃ h₁₂ hs₁ hs₂ hsep⟩
  obtain ⟨n, t, -, ht0, htmono, ht1, htT, v, hvfix, -, e, g, hgrid⟩ :=
    exists_admissible_filling_grid_of_sides (fun P : C.walls => (P : Set V))
      (fun P => C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property))
      (fun P => C.finrank_direction_add_one_of_mem_walls P.property)
      f S hS h0 h1 hSside T hT hside U hU hcover (η := 1) zero_lt_one
  -- Every grid cell lies in one of the open sets, where the local hypothesis applies.
  let cell := fun a b => (((e a b.castSucc).toPath.cons (g a.succ b)).cons
    (Quiver.reverse (e a b.succ))).cons (Quiver.reverse (g a.castSucc b))
  have hnormal : Subgroup.normalClosure
      {w | ∃ a b : Fin n, w = (cell a b).crossingWord ν} ≤ K := by
    apply Subgroup.normalClosure_le_normal
    rintro w ⟨a, b, rfl⟩
    obtain ⟨j, -, hj⟩ := hgrid a b
    refine hlocal j _ (cell a b) fun z hz => ?_
    obtain ⟨c, rfl⟩ := Quiver.Path.grid_cell_vertices_subset_range v e g a b z hz
    exact hj (subset_convexHull ℝ _ (mem_range_self c))
  have hmem := hnormal (C.crossingWord_grid_boundary_mem_normalClosure ν hν v e g)
  -- The four sides of the grid sample the four given paths through their breakpoints.
  have hbreak {a b : WallComplement (fun P : C.walls => (P : Set V))}
      (q : AdmissiblePLPath a b) (hq : q.length ≤ L) :
      ∀ k < q.length, ∃ j ≤ n, (t j : ℝ) = 1 / 2 ^ (k + 1) := fun k hk => by
    obtain ⟨j, hj, htj⟩ := htT (τ k) (Finset.mem_image_of_mem τ (Finset.mem_range.mpr
      (by omega)))
    exact ⟨j, hj, congrArg Subtype.val htj⟩
  have hrow0 := p₀.crossingWord_eq_prod_ofFn_sampling ν (fun c => v (c, 0)) t htmono ht0 ht1
    (hbreak p₀ (by omega)) (fun c => by
      rw [hvfix _ (Or.inr (Or.inr (Or.inl rfl))), Fin.val_zero, ht0, hp₀]) (fun a => e a 0)
  have hrow1 := p₁.crossingWord_eq_prod_ofFn_sampling ν (fun c => v (c, Fin.last n)) t htmono
    ht0 ht1 (hbreak p₁ (by omega)) (fun c => by
      rw [hvfix _ (Or.inr (Or.inr (Or.inr rfl))), Fin.val_last, ht1, hp₁])
    (fun a => e a (Fin.last n))
  have hcol0 := r₀.crossingWord_eq_prod_ofFn_sampling ν (fun c => v (0, c)) t htmono ht0 ht1
    (hbreak r₀ (by omega)) (fun c => by
      rw [hvfix _ (Or.inl rfl), Fin.val_zero, ht0, hr₀]) (fun b => g 0 b)
  have hcol1 := r₁.crossingWord_eq_prod_ofFn_sampling ν (fun c => v (Fin.last n, c)) t htmono
    ht0 ht1 (hbreak r₁ (by omega)) (fun c => by
      rw [hvfix _ (Or.inr (Or.inl rfl)), Fin.val_last, ht1, hr₁])
    (fun b => g (Fin.last n) b)
  dsimp only at hmem
  rw [← hrow0, ← hrow1, ← hcol0, ← hcol1] at hmem
  simpa only [Quiver.Path.crossingWord_comp, Quiver.Path.crossingWord_reverse _ ν hν,
    mul_assoc] using hmem


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
