/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Joint
public import Mei.Geometry.Convex.Polyhedron.Path.Realization
public import Mathlib.Topology.Homotopy.Path

/-!
# Homotopy invariance of crossing words modulo joint meridians

Let `C` be a finite polyhedral complex covering its ambient space and `U` an open region,
not necessarily convex. Two admissible polygonal paths with the same endpoints whose
continuous realizations are homotopic in `U` relative to the endpoints have crossing words
that agree modulo the normal closure of the words of the joint meridians in `U`
(`Quiver.Path.inv_crossingWord_mul_crossingWord_mem_normalClosure_jointMeridianWords`). This is
the relative form of the generation of loop words by joint meridians: in a convex region, the
loop case is `Quiver.Path.crossingWord_mem_normalClosure_jointMeridianWords`.

The proof fills a homotopy by an admissible grid. Its four sides are realizations of admissible
polygonal paths (`Quiver.Path.toContinuousPath`), which are affine between dyadic parameters.
`Mei.Convex.exists_admissible_filling_grid_of_sides` subdivides the square through these
breakpoints, so the grid sides sample the given paths without changing their words
(`Quiver.Path.crossingWord_eq_prod_ofFn_sampling`). Each grid cell lies in a ball inside `U`,
where the convex statement applies. The general local-to-global step for squares with
polygonal sides is `FinitePolyhedralComplex.crossingWord_boundary_mem_of_cover_of_realization`.

For a wall diagram whose labels kill the meridian words in `U`, path products along homotopic
paths in `U` therefore agree (`Mei.FiniteWallDiagram.pathProduct_eq_of_homotopy`).
-/

public section

noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- The sampling formula for an indexed sequence of vertices: the word of an admissible chain is
the reverse ordered product of the words `w a` of the sampled edges. -/
private theorem crossingWord_eq_prod_range_sampling (ν : C.walls → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) (n : ℕ)
    (v : ℕ → WallComplement (fun P : C.walls => (P : Set V))) (t : ℕ → I)
    (hmono : Monotone t) (ht0 : t 0 = 0) (htn : t n = 1)
    (hbreak : ∀ k < p.length, ∃ j ≤ n, (t j : ℝ) = 1 / 2 ^ (k + 1))
    (hv : ∀ j ≤ n, (v j).val = toContinuousPath p (t j)) (w : ℕ → FreeGroup C.walls)
    (hw : ∀ a < n, ∃ e : v a ⟶ v (a + 1), C.segmentCrossingWord ν e = w a) :
    p.crossingWord ν = ((List.range n).map w).reverse.prod := by
  induction p generalizing n v t w with
  | nil =>
    -- Every sampled edge of a constant chain is stationary.
    rw [crossingWord_nil]
    refine (List.prod_eq_one (l := ((List.range n).map w).reverse) fun g hg => ?_).symm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
    have ha' := List.mem_range.mp ha
    obtain ⟨e, he⟩ := hw a ha'
    rw [← he]
    refine C.segmentCrossingWord_eq_one ν e (Set.eq_empty_iff_forall_notMem.mpr ?_)
    rintro ⟨P, s⟩ hm
    obtain ⟨-, hP⟩ := (WallComplement.mem_crossings _ _ P s).mp hm
    rw [hv a ha'.le, hv (a + 1) ha'] at hP
    simp only [toContinuousPath_nil, Path.refl_apply, AffineMap.lineMap_same,
      AffineMap.const_apply] at hP
    exact x.notMem P hP
  | @cons u z p e ih =>
    -- Split the samples at the parameter `1 / 2` where the last edge begins.
    obtain ⟨j₀, hj₀n, hj₀⟩ := hbreak 0 (by simp)
    norm_num at hj₀
    have hle (j : ℕ) (hj : j ≤ j₀) : (t j : ℝ) ≤ 1 / 2 := hj₀ ▸ hmono hj
    have hge (j : ℕ) (hj : j₀ ≤ j) : 1 / 2 ≤ (t j : ℝ) := hj₀ ▸ hmono hj
    obtain ⟨m, rfl⟩ : ∃ m, n = j₀ + m := ⟨n - j₀, by omega⟩
    rw [List.range_add, List.map_append, List.reverse_append, List.prod_append,
      crossingWord_cons, List.map_map]
    congr 1
    · -- The second half samples the last edge.
      let s : Fin (m + 1) → I := fun a => projIcc 0 1 zero_le_one (2 * (t (j₀ + a) : ℝ) - 1)
      have hs (a : Fin (m + 1)) : (s a : ℝ) = 2 * (t (j₀ + a) : ℝ) - 1 := by
        rw [coe_projIcc]
        have := hge (j₀ + a) (by omega)
        have := (t (j₀ + a)).2.2
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      choose edge hedge using fun a : Fin m => hw (j₀ + a) (by omega)
      have hsample := C.segmentCrossingWord_eq_prod_sampling_of_endpoints ν e
        (fun a : Fin (m + 1) => v (j₀ + a)) s
        (Subtype.ext (by rw [hs]; simp [hj₀]))
        (Subtype.ext (by rw [hs]; norm_num [htn]))
        (fun a b hab => monotone_projIcc zero_le_one (by
          have : (t (j₀ + a) : ℝ) ≤ t (j₀ + b) :=
            hmono (show j₀ + (a : ℕ) ≤ j₀ + b by have := Fin.le_def.mp hab; omega)
          linarith))
        (fun a => by
          rw [hv _ (by omega), toContinuousPath_cons_apply_of_ge p e (hge _ (by omega)), hs])
        edge
      rw [hsample]
      congr 2
      have hl : (List.ofFn fun a : Fin m => w (j₀ + a.val)) =
          (List.range m).map fun a => w (j₀ + a) := by
        simpa only [List.getElem_range, List.length_range, Fin.val_cast] using
          List.ofFn_getElem_eq_map (List.range m) fun a => w (j₀ + a)
      exact (congrArg List.ofFn (funext hedge)).trans hl
    · -- The first half samples the realization of `p` at double speed.
      let s : ℕ → I := fun j => projIcc 0 1 zero_le_one (2 * (t j : ℝ))
      have hs (j : ℕ) (hj : j ≤ j₀) : s j = ⟨2 * t j, (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨(t j).2.1, hle j hj⟩⟩ := by
        refine projIcc_of_mem _ ⟨?_, ?_⟩ <;> nlinarith [(t j).2.1, hle j hj]
      refine ih j₀ v s (fun a b hab => monotone_projIcc zero_le_one (by
          have : (t a : ℝ) ≤ t b := hmono hab
          linarith))
        (Subtype.ext (by simp [s, ht0])) (Subtype.ext (by simp [s, hj₀]))
        (fun k hk => ?_) (fun j hj => ?_) w (fun a ha => hw a (by omega))
      · obtain ⟨j, hjn, hj⟩ := hbreak (k + 1) (by rw [length_cons]; omega)
        have hjj₀ : j ≤ j₀ := by
          by_contra hlt
          have h1 := hge j (by omega)
          rw [hj] at h1
          have : (1 : ℝ) / 2 ^ (k + 1 + 1) < 1 / 2 := by
            apply one_div_lt_one_div_of_lt (by norm_num)
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ < 2 ^ (k + 1 + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
          linarith
        refine ⟨j, hjj₀, ?_⟩
        rw [hs j hjj₀]
        simp only [hj, pow_succ]
        field_simp
      · rw [hv j (by omega), toContinuousPath_cons_apply_of_le p e (hle j hj), hs j hj]

/-- **Sampling a realized admissible chain.** Sample the realization of an admissible chain
at monotone parameters from `0` to `1` passing through its dyadic breakpoints `1/2^(k+1)`,
`k < p.length`, by allowed vertices joined by admissible edges. Then its word is the reverse
ordered product of the edge words. Samples may repeat. -/
theorem crossingWord_eq_prod_ofFn_sampling (ν : C.walls → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) {n : ℕ}
    (v : Fin (n + 1) → WallComplement (fun P : C.walls => (P : Set V))) (t : ℕ → I)
    (hmono : Monotone t) (ht0 : t 0 = 0) (htn : t n = 1)
    (hbreak : ∀ k < p.length, ∃ j ≤ n, (t j : ℝ) = 1 / 2 ^ (k + 1))
    (hv : ∀ j, (v j).val = toContinuousPath p (t j))
    (edge : ∀ a : Fin n, v a.castSucc ⟶ v a.succ) :
    p.crossingWord ν =
      (List.ofFn fun a => C.segmentCrossingWord ν (edge a)).reverse.prod := by
  classical
  -- Extend the samples and the edge words to all natural indices.
  let clamp : ℕ → Fin (n + 1) := fun j => ⟨min j n, by omega⟩
  let w : ℕ → FreeGroup C.walls := fun a =>
    if ha : a < n then C.segmentCrossingWord ν (edge ⟨a, ha⟩) else 1
  have hw (a : ℕ) (ha : a < n) :
      ∃ e : v (clamp a) ⟶ v (clamp (a + 1)), C.segmentCrossingWord ν e = w a := by
    have h₁ : clamp a = Fin.castSucc ⟨a, ha⟩ := Fin.ext (by simp [clamp]; omega)
    have h₂ : clamp (a + 1) = Fin.succ ⟨a, ha⟩ := Fin.ext (by simp [clamp]; omega)
    rw [h₁, h₂]
    exact ⟨edge ⟨a, ha⟩, by simp [w, ha]⟩
  have hsample := crossingWord_eq_prod_range_sampling ν p n (fun j => v (clamp j)) t hmono ht0
    htn hbreak (fun j hj => by rw [hv]; simp [clamp, min_eq_left hj]) w hw
  rw [hsample]
  congr 2
  have hl : (List.ofFn fun a : Fin n => w a.val) = (List.range n).map w := by
    simpa only [List.getElem_range, List.length_range, Fin.val_cast] using
      List.ofFn_getElem_eq_map (List.range n) w
  rw [← hl]
  exact congrArg List.ofFn (funext fun a => by simp [w, a.isLt])

end Quiver.Path

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)

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

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- **Homotopy invariance of crossing words modulo joint meridians.** For a complex covering
the ambient space, let two admissible polygonal paths with the same endpoints have realizations
that are homotopic relative to their endpoints within an open region `U`, which need not be
convex. Then their crossing words agree modulo the normal closure of the words of the joint
meridians in `U`. -/
theorem inv_crossingWord_mul_crossingWord_mem_normalClosure_jointMeridianWords
    (hC : C.support = univ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, LinearMap.ker (ν P) = (affineSpan ℝ (P : Set V)).direction)
    {U : Set V} (hUo : IsOpen U) (p q : AdmissiblePLPath x y)
    (F : p.toContinuousPath.Homotopy q.toContinuousPath) (hF : ∀ z, F z ∈ U) :
    (p.crossingWord ν)⁻¹ * q.crossingWord ν ∈
      Subgroup.normalClosure (C.jointMeridianWords ν U) := by
  -- Every point of `U` has a ball in `U`, where loop words are generated by meridians.
  choose r hr hrU using fun θ : U => Metric.isOpen_iff.mp hUo θ.val θ.property
  have hloop := C.crossingWord_boundary_mem_of_cover_of_realization ν hν
    (Subgroup.normalClosure (C.jointMeridianWords ν U)) nil nil p q F.toContinuousMap
    (fun s => by simp) (fun s => by simp) (fun s => by simp) (fun s => by simp)
    (fun θ : U => Metric.ball θ.val (r θ)) (fun _ => Metric.isOpen_ball)
    (fun z => ⟨⟨F z, hF z⟩, Metric.mem_ball_self (hr _)⟩)
    (fun θ w l hl => Subgroup.normalClosure_mono (C.jointMeridianWords_mono ν (hrU θ))
      (l.crossingWord_mem_normalClosure_jointMeridianWords hC ν hν Metric.isOpen_ball
        (convex_ball _ _) hl))
  simpa only [crossingWord_comp, crossingWord_reverse _ ν hν, crossingWord_nil, inv_one,
    mul_one, one_mul] using hloop

end Quiver.Path
