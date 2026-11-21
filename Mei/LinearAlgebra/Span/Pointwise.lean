/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.Abel

/-!
# Pointwise sums of sets with spans

For a set `P` in a module `M` over a ring `R`, this file describes the pointwise sum `P + K` of
`P` with a submodule `K`:

* `Submodule.mem_add_span_singleton_iff`: `y ∈ P + R ∙ v` if and only if `y + a • v ∈ P` for
  some `a : R`;
* `Submodule.add_span_singleton_eq_setOf_exists_nonneg`: over an ordered ring, adding the line
  `R ∙ v` is adding the ray through `v` and then the ray through `-v`;
* `Submodule.add_span_induction`: a property of sets that is preserved by adding each line
  `R ∙ v` with `v ∈ s` is preserved by adding `span R s`, provided `span R s` is finitely
  generated;
* `LinearMap.preimage_inr_add_ker_snd`: the image of `G ⊆ M × M₂` under the second projection is
  the slice at `0` of `G + ker snd`.

These identities reduce sums with finitely generated submodules, and linear projections, to
finitely many one-parameter eliminations.
-/

public section

open scoped Pointwise

namespace Submodule

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A point lies in the sum of `P` and the line `R ∙ v` exactly when some translate of it along
`v` lies in `P`. -/
theorem mem_add_span_singleton_iff {P : Set M} {v y : M} :
    y ∈ P + ((R ∙ v : Submodule R M) : Set M) ↔ ∃ a : R, y + a • v ∈ P := by
  simp only [Set.mem_add, SetLike.mem_coe, mem_span_singleton]
  constructor
  · rintro ⟨x, hx, _, ⟨a, rfl⟩, rfl⟩
    exact ⟨-a, by simpa [add_assoc] using hx⟩
  · rintro ⟨a, ha⟩
    exact ⟨y + a • v, ha, -a • v, ⟨-a, rfl⟩, by simp [neg_smul]⟩

/-- Over an ordered ring, the sum of `P` and the line `R ∙ v` is obtained by first adding the
ray through `v` (the set of `z` with `z + t • v ∈ P` for some `t ≥ 0`) and then the ray through
`-v`. -/
theorem add_span_singleton_eq_setOf_exists_nonneg [LinearOrder R] [IsOrderedRing R]
    (P : Set M) (v : M) :
    P + ((R ∙ v : Submodule R M) : Set M) =
      {y | ∃ s : R, 0 ≤ s ∧ y + s • -v ∈ {z | ∃ t : R, 0 ≤ t ∧ z + t • v ∈ P}} := by
  ext y
  simp only [mem_add_span_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · -- A nonnegative coefficient uses the first ray only, a negative one the second ray only.
    rintro ⟨a, ha⟩
    rcases le_total 0 a with h | h
    · exact ⟨0, le_rfl, a, h, by simpa using ha⟩
    · exact ⟨-a, neg_nonneg.mpr h, 0, le_rfl, by simpa using ha⟩
  · rintro ⟨s, -, t, -, hst⟩
    have he : y + (t - s) • v = y + s • -v + t • v := by rw [smul_neg, sub_smul]; abel
    exact ⟨t - s, he ▸ hst⟩

end Ring

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Let `p` be a property of sets that is preserved by adding each line `R ∙ v` with `v ∈ s`.
If `span R s` is finitely generated, then `p` is preserved by adding `span R s`. The set `s`
itself may be infinite. -/
theorem add_span_induction {p : Set M → Prop} {s : Set M} (hs : (span R s).FG)
    (hline : ∀ Q : Set M, p Q → ∀ v ∈ s, p (Q + ((R ∙ v : Submodule R M) : Set M)))
    {P : Set M} (hP : p P) : p (P + (span R s : Set M)) := by
  classical
  obtain ⟨t, hts, heq⟩ := (fg_span_iff_fg_span_finset_subset s).mp hs
  rw [heq]
  clear heq
  -- Add the lines through the finitely many generators in `t ⊆ s` one at a time.
  induction t using Finset.induction_on generalizing P with
  | empty => simpa using hP
  | insert v t _ ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at hts
    rw [Finset.coe_insert, span_insert, coe_sup, ← add_assoc]
    exact ih (hline P hP v hts.1) hts.2

end Semiring

end Submodule

namespace LinearMap

variable {M M₂ : Type*} [AddCommGroup M] [AddCommMonoid M₂]

/-- The image of `G ⊆ M × M₂` under the second projection consists of the `w` with `(0, w)` in
`G + ker snd`. -/
theorem preimage_inr_add_ker_snd (R : Type*) [Semiring R] [Module R M] [Module R M₂]
    (G : Set (M × M₂)) :
    inr R M M₂ ⁻¹' (G + (ker (snd R M M₂) : Set (M × M₂))) = Prod.snd '' G := by
  ext w
  simp only [Set.mem_preimage, Set.mem_add, SetLike.mem_coe, mem_ker, snd_apply, inr_apply,
    Set.mem_image]
  constructor
  · rintro ⟨p, hp, k, hk, he⟩
    exact ⟨p, hp, by simpa [hk] using congrArg Prod.snd he⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, (-p.1, 0), rfl, Prod.ext (by simp) (by simp)⟩

end LinearMap
