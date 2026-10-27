/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Alternating forms on edge frames of simplices and their faces

The edge frame of points `v : Fin (k + 2) → M` is `(v 1 - v 0, …, v (k + 1) - v 0)`. Its
`l`th face omits `v l`, and has the edge frame of `v ∘ l.succAbove`. Let `p = ∑ j, b j • v j`
with `∑ j, b j = 1`, and let `q` lie in the affine span of the `l`th face. An alternating form
`α` in `k + 1` arguments satisfies the face formula
`α (q - p, face frame) = (-1) ^ l * b l * α (edge frame)`.

For an interior point `p` and a point `q` on face `l`, the vector `q - p` leaves the simplex
through that face. Thus the formula compares the orientation induced on face `l` by the
outward vector `q - p` with the orientation of the whole simplex. The sign `(-1) ^ l` is the
sign of face `l` in the simplicial boundary `∂τ = ∑ l, (-1) ^ l τ ∘ δ_l`. This is the sign
computation in a Stokes formula for intersection numbers with affine simplices.

The face formula allows arbitrary commutative rings and modules; the two auxiliary vanishing
and invariance lemmas also hold over semirings.
-/

public section

open Function Set Submodule

namespace AlternatingMap

section Semiring

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] {n : ℕ}

/-- An alternating map vanishes when the first argument lies in the span of the others. -/
theorem map_vecCons_eq_zero_of_mem_span (f : M [⋀^Fin (n + 1)]→ₗ[R] N) {x : M}
    {v : Fin n → M} (hx : x ∈ span R (range v)) : f (Matrix.vecCons x v) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact f.map_eq_zero_of_eq _ (by simp) (Fin.succ_ne_zero i).symm
  | zero => exact f.map_coord_zero 0 (by simp)
  | add y z _ _ hy hz => simp [map_vecCons_add, hy, hz]
  | smul c y _ hy => simp [map_vecCons_smul, hy]

/-- Adding multiples of the first argument to the others does not change an alternating map. -/
theorem map_vecCons_tail_add_smul_head (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (x : M) (v : Fin n → M)
    (c : Fin n → R) : f (Matrix.vecCons x fun i => v i + c i • x) = f (Matrix.vecCons x v) := by
  classical
  -- Add the multiples one coordinate at a time; each extra term repeats the head.
  have h (s : Finset (Fin n)) :
      f (Matrix.vecCons x (s.piecewise (fun i => v i + c i • x) v)) =
        f (Matrix.vecCons x v) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      -- `vecCons` is `Fin.cons`, so `Fin.cons_update` moves the update to index `i.succ`.
      rw [Finset.piecewise_insert, Matrix.vecCons, Fin.cons_update, f.map_update_add,
        f.map_update_smul]
      have hz : f (update (Fin.cons x (s.piecewise (fun j => v j + c j • x) v))
          i.succ x) = 0 :=
        f.map_eq_zero_of_eq _
          (by simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]) (Fin.succ_ne_zero i)
      rw [hz, smul_zero, add_zero, ← Fin.cons_update,
        ← s.piecewise_eq_of_notMem (fun j => v j + c j • x) v hi, update_eq_self]
      exact ih
  simpa using h Finset.univ

end Semiring

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- **Face formula for edge frames.** Let `y` lie in the affine span of the `l`th face of the
points `v`, and let `b` be affine weights. Then `y - ∑ j, b j • v j`, followed by the edge frame
of the `l`th face, evaluates to `(-1) ^ l * b l` times the value on the edge frame of `v`. -/
theorem map_vecCons_sub_faceEdgeFrame (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (v : Fin (n + 2) → M)
    (l : Fin (n + 2)) {b : Fin (n + 2) → R} (hb : ∑ j, b j = 1) {y : M}
    (hy : y ∈ affineSpan R (range (v ∘ l.succAbove))) :
    f (Matrix.vecCons (y - ∑ j, b j • v j)
        fun i : Fin n => v (l.succAbove i.succ) - v (l.succAbove 0)) =
      ((-1) ^ (l : ℕ) * b l) • f fun j : Fin (n + 1) => v j.succ - v 0 := by
  set r := l.succAbove 0
  set e : Fin n → M := fun i => v (l.succAbove i.succ) - v r with he
  set S := span R (range e)
  -- Every edge of the face starting at its first vertex lies in `S`.
  have hS (m : Fin (n + 1)) : v (l.succAbove m) - v r ∈ S := by
    cases m using Fin.cases with
    | zero => simp [r]
    | succ i => exact subset_span ⟨i, rfl⟩
  have hyS : y - v r ∈ S := by
    have hmem := AffineSubspace.vsub_mem_direction hy
      (mem_affineSpan R (mem_range_self (0 : Fin (n + 1))))
    rw [direction_affineSpan, vectorSpan_range_eq_span_range_vsub_right R _ 0] at hmem
    exact span_le.mpr (range_subset_iff.mpr fun m => hS m) hmem
  -- Decompose `y - p` into a multiple of the omitted edge and a vector tangent to the face.
  have hdecomp : y - ∑ j, b j • v j =
      b l • (v r - v l) + ((y - v r) - ∑ m, b (l.succAbove m) • (v (l.succAbove m) - v r)) := by
    have hv : ∑ j, b j • v j = ∑ j, b j • (v j - v r) + v r := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hb, one_smul,
        sub_add_cancel]
    rw [hv, Fin.sum_univ_succAbove _ l]
    simp only [smul_sub]
    abel
  have htan : (y - v r) - ∑ m, b (l.succAbove m) • (v (l.succAbove m) - v r) ∈ S :=
    S.sub_mem hyS (S.sum_mem fun m _ => S.smul_mem _ (hS m))
  -- It remains to compare the omitted edge with the edge frame of the whole simplex.
  have hkey : f (Matrix.vecCons (v r - v l) e) =
      ((-1) ^ (l : ℕ) : R) • f fun j : Fin (n + 1) => v j.succ - v 0 := by
    cases l using Fin.cases with
    | zero =>
      have hframe : e = fun i => (v i.succ.succ - v 0) + (-1 : R) • (v 1 - v 0) := by
        ext i
        simp only [he, r, Fin.succAbove_zero, Fin.succ_zero_eq_one]
        module
      have hr : r = 1 := by simp [r]
      rw [hframe, hr, map_vecCons_tail_add_smul_head, Fin.val_zero, pow_zero, one_smul]
      exact congrArg f (funext fun j => by cases j using Fin.cases <;> simp)
    | succ j =>
      have hframe : e = j.removeNth fun i => v i.succ - v 0 := by
        ext i
        simp [he, r, Fin.removeNth]
      have hr : r = 0 := Fin.succ_succAbove_zero j
      have hins := Fin.insertNth_self_removeNth j fun i : Fin (n + 1) => v i.succ - v 0
      beta_reduce at hins
      rw [hframe, hr, ← neg_sub, ← neg_one_smul R (v j.succ - v 0), map_vecCons_smul,
        ← neg_one_pow_smul_map_insertNth f j, hins, Fin.val_succ]
      module
  rw [hdecomp, ← curryLeft_apply_apply, map_add, add_apply, curryLeft_apply_apply,
    curryLeft_apply_apply, f.map_vecCons_eq_zero_of_mem_span htan, add_zero, map_vecCons_smul,
    hkey, smul_smul, mul_comm]

end AlternatingMap
