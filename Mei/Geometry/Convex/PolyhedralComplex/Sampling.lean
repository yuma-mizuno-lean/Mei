/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.PathSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.Grid

/-!
# Crossing words of sampled affine segments

Sampling an admissible affine segment at a finite monotone sequence of allowed
points preserves its crossing word. The parameter sequence need not be strictly
increasing: repeated samples contribute stationary edges with empty words. The
formula uses the reverse ordered product, with the first crossing on the right.
It compares the boundary edges of an affine filling with the sampled sides of
an admissible grid without imposing any relations on the wall labels.

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

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}

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
