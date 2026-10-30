/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.Grid
public import Mei.Geometry.Convex.Polyhedron.Path.Realization

/-!
# Crossing words of sampled affine segments and polygonal paths

Sampling an admissible affine segment at a finite monotone sequence of allowed
points preserves its crossing word. The parameter sequence need not be strictly
increasing: repeated samples contribute stationary edges with empty words. The
formula uses the reverse ordered product, with the first crossing on the right.
It compares the boundary edges of an affine filling with the sampled sides of
an admissible grid without imposing any relations on the wall labels.

`Quiver.Path.crossingWord_eq_prod_ofFn_sampling` extends this comparison to the
continuous realization of an admissible polygonal chain. The samples must pass
through its dyadic breakpoints.

`FinitePolyhedralComplex.crossingWord_boundary_mem_normalClosure_of_sampling`
places the original four-edge boundary word in the normal closure of the grid
cell words. This boundary comparison requires each wall form `ν P` to have
kernel equal to the direction of the wall's affine span, so reversing an edge
inverts its word. No transversality of a filling, geometric nondegeneracy, or
consistency of a diagram is needed.
-/

public section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)

/-- The word of an admissible affine segment equals the reverse ordered product
of its sampled subsegment words. Samples may repeat, and the original segment
may be stationary. The supplied edges can be any admissible segments with the
indicated endpoints. -/
theorem segmentCrossingWord_eq_prod_sampling {n : ℕ}
    (v : Fin (n + 1) → WallComplement (fun P : C.walls => (P : Set V)))
    (e : v 0 ⟶ v (Fin.last n)) (t : Fin (n + 1) → unitInterval)
    (hmono : Monotone t)
    (hv : ∀ j, (v j).val = AffineMap.lineMap (v 0).val (v (Fin.last n)).val (t j : ℝ))
    (edge : ∀ a : Fin n, v a.castSucc ⟶ v a.succ) :
    C.segmentCrossingWord ν e =
      (List.ofFn (fun a : Fin n => C.segmentCrossingWord ν (edge a))).reverse.prod := by
  -- Use `WallComplement.AdmissibleSegment.subsegment` to form prefixes, then
  -- telescope their words using `segmentCrossingWord_subdivide`, including its endpoint cases.
  let initialSeg (j : Fin (n + 1)) : v 0 ⟶ v j :=
    ⟨e.down.subsegment ⟨le_rfl, zero_le_one⟩ (t j).property
      (AffineMap.lineMap_apply_zero _ _).symm (hv j)⟩
  have hstep (a : Fin n) : C.segmentCrossingWord ν (initialSeg a.succ) =
      C.segmentCrossingWord ν (edge a) * C.segmentCrossingWord ν (initialSeg a.castSucc) := by
    have hle : (t a.castSucc : ℝ) ≤ t a.succ := hmono a.castSucc_le_succ
    -- Rescale the prefix interval; a zero-length interval uses parameter zero.
    by_cases hz : (t a.succ : ℝ) = 0
    · have hz' : (t a.castSucc : ℝ) = 0 := le_antisymm (hle.trans_eq hz) (t _).property.1
      apply C.segmentCrossingWord_subdivide ν (initialSeg a.succ) (initialSeg a.castSucc) (edge a)
        (t := 0) ⟨le_rfl, zero_le_one⟩
      simp only [AffineMap.lineMap_apply_zero, hv a.castSucc, hz']
    · have hpos : 0 < (t a.succ : ℝ) := lt_of_le_of_ne (t _).property.1 (Ne.symm hz)
      apply C.segmentCrossingWord_subdivide ν (initialSeg a.succ) (initialSeg a.castSucc) (edge a)
        (t := (t a.castSucc : ℝ) / t a.succ)
        ⟨div_nonneg (t _).property.1 hpos.le, (div_le_one hpos).mpr hle⟩
      rw [hv a.castSucc, hv a.succ, AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ hz]
  -- Accumulate prefixes, placing each new edge on the left.
  have hprod (m : ℕ) (hm : m ≤ n) :
      (List.ofFn (fun a : Fin m =>
        C.segmentCrossingWord ν (edge ⟨a.val, lt_of_lt_of_le a.isLt hm⟩))).reverse.prod =
          C.segmentCrossingWord ν (initialSeg ⟨m, by omega⟩) := by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [List.ofFn_succ', List.concat_eq_append, List.reverse_append,
        List.reverse_singleton, List.prod_append, List.prod_singleton]
      exact (congrArg (C.segmentCrossingWord ν (edge ⟨m, by omega⟩) * ·)
        (ih (by omega))).trans (hstep ⟨m, by omega⟩).symm
  exact (hprod n le_rfl).symm

/-- A segment with independently specified endpoints has the reverse product of
its sampled subsegment words when the first and last parameters are zero and one.
Repeated parameters and stationary segments are allowed. -/
theorem segmentCrossingWord_eq_prod_sampling_of_endpoints {n : ℕ}
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (e : x ⟶ y) (v : Fin (n + 1) → WallComplement (fun P : C.walls => (P : Set V)))
    (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hmono : Monotone t)
    (hv : ∀ j, (v j).val = AffineMap.lineMap x.val y.val (t j : ℝ))
    (edge : ∀ a : Fin n, v a.castSucc ⟶ v a.succ) :
    C.segmentCrossingWord ν e =
      (List.ofFn (fun a : Fin n => C.segmentCrossingWord ν (edge a))).reverse.prod := by
  have hx : v 0 = x := by ext; simpa [ht0] using hv 0
  have hy : v (Fin.last n) = y := by ext; simpa [ht1] using hv (Fin.last n)
  subst x
  subst y
  exact C.segmentCrossingWord_eq_prod_sampling ν v e t hmono hv edge

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}

variable {x y : WallComplement (fun P : C.walls => (P : Set V))}

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
    have hx (j : ℕ) (hj : j ≤ n) : v j = x := by
      apply WallComplement.ext
      simpa only [toContinuousPath_nil, Path.refl_apply] using hv j hj
    suffices ∀ e : v a ⟶ v (a + 1), C.segmentCrossingWord ν e = 1 from this e
    rw [hx a ha'.le, hx (a + 1) ha']
    exact C.segmentCrossingWord_self ν
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

/-- An initial sequence of admissible edges sampling an affine segment has the
same word as that segment. Only samples through the specified endpoint matter. -/
theorem crossingWord_ofSeq_eq_segmentCrossingWord
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (x : ℕ → WallComplement (fun P : C.walls => (P : Set V)))
    (edge : ∀ j, x j ⟶ x (j + 1)) (n : ℕ) (e : x 0 ⟶ x n)
    (t : ℕ → unitInterval) (hmono : Monotone t)
    (hx : ∀ j ≤ n, (x j).val = AffineMap.lineMap (x 0).val (x n).val (t j : ℝ)) :
    (ofSeq x edge n).crossingWord ν = C.segmentCrossingWord ν e := by
  have hs := C.segmentCrossingWord_eq_prod_sampling ν
    (fun j : Fin (n + 1) => x j.val) e (fun j => t j.val)
    (fun _ _ hab => hmono hab) (fun j => hx j.val (by omega)) (fun a => edge a.val)
  let w := fun j => C.segmentCrossingWord ν (edge j)
  have hl : (List.ofFn fun a : Fin n => w a.val) = (List.range n).map w := by
    simpa only [List.getElem_range, List.length_range, Fin.val_cast] using
      List.ofFn_getElem_eq_map (List.range n) w
  dsimp only [w] at hl
  rw [hl, List.prod_reverse_noncomm, List.map_map] at hs
  exact (crossingWord_ofSeq x edge n ν).trans hs.symm

end Quiver.Path

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- If the four sides of an admissible grid sample four original affine
segments, the original four-edge loop word lies in the normal closure of the
grid cell words. Interior vertices are unrestricted, and samples may repeat.
Thus local cell relations apply to the original boundary, without moving it. -/
theorem crossingWord_boundary_mem_normalClosure_of_sampling (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (x : ℕ → ℕ → WallComplement (fun P : C.walls => (P : Set V)))
    (e : ∀ a b, x a b ⟶ x a (b + 1))
    (f : ∀ a b, x a b ⟶ x (a + 1) b) (m n : ℕ)
    (bottom : x 0 0 ⟶ x 0 n) (right : x 0 n ⟶ x m n)
    (top : x m 0 ⟶ x m n) (left : x 0 0 ⟶ x m 0)
    (s t : ℕ → unitInterval) (hs : Monotone s) (ht : Monotone t)
    (hrow : ∀ a ∈ ({0, m} : Finset ℕ), ∀ b ≤ n,
      (x a b).val = AffineMap.lineMap (x a 0).val (x a n).val (t b : ℝ))
    (hcol : ∀ b ∈ ({0, n} : Finset ℕ), ∀ a ≤ m,
      (x a b).val = AffineMap.lineMap (x 0 b).val (x m b).val (s a : ℝ)) :
    (((bottom.toPath.cons right).cons (Quiver.reverse top)).cons
      (Quiver.reverse left)).crossingWord ν ∈
        Subgroup.normalClosure {g | ∃ a < m, ∃ b < n,
          g = ((((e a b).toPath.cons (f a (b + 1))).cons
            (Quiver.reverse (e (a + 1) b))).cons (Quiver.reverse (f a b))).crossingWord ν} := by
  have hb := C.segmentCrossingWord_eq_prod_sampling ν
    (fun b : Fin (n + 1) => x 0 b.val) bottom (fun b => t b.val)
    (fun _ _ hab => ht hab) (fun b => hrow 0 (by simp) b.val (by omega))
    (fun b => e 0 b.val)
  have hr := C.segmentCrossingWord_eq_prod_sampling ν
    (fun a : Fin (m + 1) => x a.val n) right (fun a => s a.val)
    (fun _ _ hab => hs hab) (fun a => hcol n (by simp) a.val (by omega))
    (fun a => f a.val n)
  have ht' := C.segmentCrossingWord_eq_prod_sampling ν
    (fun b : Fin (n + 1) => x m b.val) top (fun b => t b.val)
    (fun _ _ hab => ht hab) (fun b => hrow m (by simp) b.val (by omega))
    (fun b => e m b.val)
  have hl := C.segmentCrossingWord_eq_prod_sampling ν
    (fun a : Fin (m + 1) => x a.val 0) left (fun a => s a.val)
    (fun _ _ hab => hs hab) (fun a => hcol 0 (by simp) a.val (by omega))
    (fun a => f a.val 0)
  -- Restrict to the finite rectangle, keeping the original boundary orientation.
  have hgrid := C.crossingWord_grid_boundary_mem_normalClosure ν hν
    (fun p : Fin (n + 1) × Fin (m + 1) => x p.2.val p.1.val)
    (fun a b => e b.val a.val) (fun a b => f b.val a.val)
  -- `show` supplies the source set that `normalClosure_mono` cannot infer from
  -- the target alone: grid cells use finite column-row indices, while the target
  -- uses bounded natural row-column indices. The inclusion swaps these indices.
  have hmem := Subgroup.normalClosure_mono (show
      {g | ∃ (a : Fin n) (b : Fin m), g =
        ((((e b.val a.val).toPath.cons (f b.val (a.val + 1))).cons
          (Quiver.reverse (e (b.val + 1) a.val))).cons
            (Quiver.reverse (f b.val a.val))).crossingWord ν} ⊆
      {g | ∃ a < m, ∃ b < n, g =
        ((((e a b).toPath.cons (f a (b + 1))).cons
          (Quiver.reverse (e (a + 1) b))).cons
            (Quiver.reverse (f a b))).crossingWord ν} from by
      rintro g ⟨a, b, rfl⟩
      exact ⟨b.val, b.isLt, a.val, a.isLt, rfl⟩) hgrid
  simp only [Fin.val_zero, Fin.val_last] at hmem
  rw [← hb, ← hr, ← ht', ← hl] at hmem
  simpa only [Quiver.Path.crossingWord_comp, Quiver.Path.crossingWord_cons,
    Quiver.Hom.toPath, Quiver.Path.crossingWord_nil, mul_one,
    Quiver.Path.crossingWord_reverse _ ν hν, C.segmentCrossingWord_reverse ν hν,
    Fin.val_zero, Fin.val_last, mul_assoc] using hmem

end Mei.FinitePolyhedralComplex
