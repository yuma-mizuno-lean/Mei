/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision
public import Mei.Geometry.Convex.Polyhedron.SimultaneousPath

/-!
# Polygonal structure of realized admissible paths

The continuous realization `Quiver.Path.toContinuousPath` of an admissible chain with `ℓ`
edges traverses its last edge on `[1/2, 1]`, the edge before on `[1/4, 1/2]`, and so on, and it
is constant on `[0, 1/2^ℓ]`. Consequently:

* at every dyadic time `1/2^(k+1)` the realization is at an allowed point
  (`Quiver.Path.toContinuousPath_notMem_of_eq_half_pow`);
* for a countable wall family, it meets the walls at only countably many parameters
  (`Quiver.Path.countable_setOf_toContinuousPath_mem`);
* if every wall is closed, between two allowed parameters that no dyadic time `1/2^(k+1)`,
  `k < ℓ`, separates, it is an admissible straight segment
  (`Quiver.Path.toContinuousPath_mem_admissiblePairs`).

These facts let a continuous square whose sides are realized admissible chains be subdivided
by an admissible grid whose boundary edges lie on those sides.
-/

public section

open Set Mei.Convex
open scoped unitInterval

namespace Quiver.Path

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y z : WallComplement W}

/-- On the first half of the parameter interval, the realization of `p.cons e` is the
realization of `p` at double speed. -/
theorem toContinuousPath_cons_apply_of_le (p : AdmissiblePLPath x y) (e : y ⟶ z)
    {s : I} (hs : (s : ℝ) ≤ 1 / 2) :
    toContinuousPath (p.cons e) s =
      toContinuousPath p ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ := by
  rw [toContinuousPath_cons, Path.trans_apply]
  simp only [hs, ↓reduceDIte]

/-- On the second half of the parameter interval, the realization of `p.cons e` runs along
the last edge. -/
theorem toContinuousPath_cons_apply_of_ge (p : AdmissiblePLPath x y) (e : y ⟶ z)
    {s : I} (hs : 1 / 2 ≤ (s : ℝ)) :
    toContinuousPath (p.cons e) s = AffineMap.lineMap y.val z.val (2 * (s : ℝ) - 1) := by
  rcases hs.lt_or_eq with hs | hs
  · rw [toContinuousPath_cons, Path.trans_apply]
    simp only [not_le.mpr hs, ↓reduceDIte, Path.segment_apply]
  · rw [toContinuousPath_cons_apply_of_le p e hs.ge]
    have h1 : (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs.ge⟩⟩ : I) = 1 :=
      Subtype.ext (by simp only [Set.Icc.coe_one]; linarith)
    rw [h1, Path.target, ← hs]
    norm_num

/-- At every dyadic time `1/2^(k+1)` the realization of an admissible chain is at an allowed
point: a vertex of the chain, or its initial point on the constant initial piece. -/
theorem toContinuousPath_notMem_of_eq_half_pow (p : AdmissiblePLPath x y) (k : ℕ) {s : I}
    (hs : (s : ℝ) = 1 / 2 ^ (k + 1)) (i : ι) : toContinuousPath p s ∉ W i := by
  induction p generalizing k s with
  | nil =>
    rw [toContinuousPath_nil, Path.refl_apply]
    exact x.notMem i
  | @cons u v p e ih =>
    rcases k with _ | k
    · rw [toContinuousPath_cons_apply_of_ge p e (by rw [hs]; norm_num)]
      have h0 : 2 * (s : ℝ) - 1 = 0 := by rw [hs]; norm_num
      rw [h0, AffineMap.lineMap_apply_zero]
      exact u.notMem i
    · have hle : (s : ℝ) ≤ 1 / 2 := by
        rw [hs]
        have hk : 1 ≤ k + 1 + 1 := by omega
        exact one_div_le_one_div_of_le (by norm_num) (by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
      rw [toContinuousPath_cons_apply_of_le p e hle]
      exact ih k (by simp only [hs, pow_succ]; field_simp)

/-- An admissible chain for countably many walls meets them at only countably many
parameters of its realization. -/
theorem countable_setOf_toContinuousPath_mem [Countable ι] (p : AdmissiblePLPath x y) :
    {s : ℝ | ∃ hs : s ∈ Icc (0 : ℝ) 1, ∃ i, toContinuousPath p ⟨s, hs⟩ ∈ W i}.Countable := by
  induction p with
  | nil =>
    refine Set.countable_empty.mono fun s ⟨hs, i, hi⟩ => ?_
    rw [toContinuousPath_nil, Path.refl_apply] at hi
    exact x.notMem i hi
  | @cons u v p e ih =>
    -- Parameters on the first half come from `p`, the others from crossings of `e`.
    refine ((ih.image fun s => s / 2).union
      (e.down.countable_crossings.image fun a => (a.2 + 1) / 2)).mono ?_
    rintro s ⟨hs, i, hi⟩
    by_cases hle : s ≤ 1 / 2
    · rw [toContinuousPath_cons_apply_of_le p e (s := ⟨s, hs⟩) hle] at hi
      exact Or.inl ⟨2 * s, ⟨_, i, hi⟩, by ring⟩
    · rw [toContinuousPath_cons_apply_of_ge p e (s := ⟨s, hs⟩) (le_of_not_ge hle)] at hi
      refine Or.inr ⟨(i, 2 * s - 1), (WallComplement.mem_crossings u v i _).mpr
        ⟨⟨by linarith, by linarith [hs.2]⟩, hi⟩, by ring⟩

/-- Between two allowed parameters that no dyadic time `1/2^(k+1)`, `k < L`, separates, the
realization of an admissible chain with at most `L` edges is an admissible straight segment.
The walls must be closed, so that a constant piece is admissible. -/
theorem toContinuousPath_mem_admissiblePairs (hclosed : ∀ i, IsClosed (W i))
    (p : AdmissiblePLPath x y) {L : ℕ} (hL : p.length ≤ L) {s₁ s₂ : I} (h₁₂ : s₁ ≤ s₂)
    (hsep : ∀ k < L, 1 / 2 ^ (k + 1) ≤ (s₁ : ℝ) ∨ (s₂ : ℝ) ≤ 1 / 2 ^ (k + 1))
    (h₁ : ∀ i, toContinuousPath p s₁ ∉ W i) (h₂ : ∀ i, toContinuousPath p s₂ ∉ W i) :
    (toContinuousPath p s₁, toContinuousPath p s₂) ∈ admissiblePairs W := by
  induction p generalizing L s₁ s₂ with
  | nil =>
    have hx : x.val ∉ singularSupport W := fun hs => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (singularSupport_subset_iUnion W hclosed hs)
      exact x.notMem i hi
    simpa only [toContinuousPath_nil, Path.refl_apply] using
      (mem_admissiblePairs_iff x x).mpr (WallComplement.AdmissibleSegment.refl x hx)
  | @cons u v p e ih =>
    rw [length_cons] at hL
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have h₁₂' : (s₁ : ℝ) ≤ s₂ := h₁₂
    rcases hsep 0 (Nat.zero_lt_succ L) with hhalf | hhalf
    · -- Both parameters lie on the last edge.
      have hs₁ : 1 / 2 ≤ (s₁ : ℝ) := by simpa using hhalf
      have hs₂ : 1 / 2 ≤ (s₂ : ℝ) := hs₁.trans h₁₂'
      rw [toContinuousPath_cons_apply_of_ge p e hs₁] at h₁ ⊢
      rw [toContinuousPath_cons_apply_of_ge p e hs₂] at h₂ ⊢
      exact (mem_admissiblePairs_iff ⟨_, h₁⟩ ⟨_, h₂⟩).mpr
        (e.down.subsegment ⟨by linarith, by linarith [s₁.2.2]⟩
          ⟨by linarith, by linarith [s₂.2.2]⟩ rfl rfl)
    · -- Both parameters lie on the realization of `p`, run at double speed.
      have hs₂ : (s₂ : ℝ) ≤ 1 / 2 := by simpa using hhalf
      have hs₁ : (s₁ : ℝ) ≤ 1 / 2 := h₁₂'.trans hs₂
      rw [toContinuousPath_cons_apply_of_le p e hs₁] at h₁ ⊢
      rw [toContinuousPath_cons_apply_of_le p e hs₂] at h₂ ⊢
      refine ih (L := L) (by omega) (Subtype.mk_le_mk.mpr (by linarith)) (fun k hk => ?_) h₁ h₂
      have hpow : (1 : ℝ) / 2 ^ (k + 1 + 1) = 1 / 2 ^ (k + 1) / 2 := by
        rw [pow_succ _ (k + 1)]
        ring
      rcases hsep (k + 1) (by omega) with h | h
      · rw [hpow] at h
        exact Or.inl (by linarith : 1 / 2 ^ (k + 1) ≤ 2 * (s₁ : ℝ))
      · rw [hpow] at h
        exact Or.inr (by linarith : 2 * (s₂ : ℝ) ≤ 1 / 2 ^ (k + 1))

end Quiver.Path
