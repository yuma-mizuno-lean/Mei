/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Grading
public import TauCeti.Algebra.Lie.LowerCentralSeries
public import Mei.Algebra.DirectSum.Degree

/-!
# Word length and the lower central series of a free Lie algebra

Mathlib numbers the lower central series from zero. Its `k`-th term in a
free Lie algebra is precisely the span of bracketed words with at least `k + 1`
leaves. This description holds over every commutative ring.

The word bound uses `TauCeti.lie_lowerCentralSeries_le`; the converse follows
from the defining recursion of the lower central series and Lie generation.
-/

public section

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] {S : Type*}

local notation "F" => _root_.FreeLieAlgebra R S

/-- A bracketed word of length `n` belongs to lower-central order `n - 1`. -/
theorem word_mem_lowerCentralSeries (w : FreeMagma S) :
    word R w ∈ LieModule.lowerCentralSeries R F F (w.length - 1) := by
  induction w with
  | ih1 s => simp only [FreeMagma.length, Nat.sub_self, LieModule.lowerCentralSeries_zero]; trivial
  | ih2 u v hu hv =>
    have h := TauCeti.lie_lowerCentralSeries_le F (u.length - 1) (v.length - 1)
      (LieSubmodule.lie_mem_lie hu hv)
    have hp := u.length_pos
    have hq := v.length_pos
    have he : u.length - 1 + (v.length - 1) + 1 = (u.length + v.length) - 1 := by omega
    simpa only [word_mul, FreeMagma.length, he] using h

private theorem lie_mem_span_words_above {k l : ℕ} {x y : F}
    (hx : x ∈ Submodule.span R (word R '' {w : FreeMagma S | k < w.length}))
    (hy : y ∈ Submodule.span R (word R '' {w : FreeMagma S | l < w.length})) :
    ⁅x, y⁆ ∈ Submodule.span R (word R '' {w : FreeMagma S | k + l + 1 < w.length}) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      rw [← word_mul]
      exact Submodule.subset_span ⟨u * v, by
        simp only [Set.mem_ofPred_eq, FreeMagma.length] at hu hv ⊢
        omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [lie_add] using add_mem hx hy
    | smul r x _ hx => simpa only [lie_smul] using Submodule.smul_mem _ r hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_lie] using add_mem hx hy
  | smul r x _ hx => simpa only [smul_lie] using Submodule.smul_mem _ r hx

/-- The zero-based lower central series is exactly the span of sufficiently
long bracketed words. -/
theorem lowerCentralSeries_toSubmodule_eq_span_words (k : ℕ) :
    (LieModule.lowerCentralSeries R F F k).toSubmodule =
      Submodule.span R (word R '' {w : FreeMagma S | k < w.length}) := by
  apply le_antisymm
  · induction k with
    | zero =>
      simp only [FreeMagma.length_pos, Set.ofPred_true, Set.image_univ, span_range_word, le_top]
    | succ k ih =>
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, y, hy, rfl⟩
      have hx : x ∈ Submodule.span R (word R '' {w : FreeMagma S | 0 < w.length}) := by
        simp only [FreeMagma.length_pos, Set.ofPred_true, Set.image_univ,
          span_range_word, Submodule.mem_top]
      simpa only [zero_add, SetLike.mem_coe] using lie_mem_span_words_above R hx (ih hy)
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw
    exact LieModule.antitone_lowerCentralSeries R F F (by omega : k ≤ w.length - 1)
      (word_mem_lowerCentralSeries R w)

/-- Lower-central order `k` is the degree tail beginning at word length `k + 1`. -/
theorem lowerCentralSeries_toSubmodule_eq_degreeTail (k : ℕ) :
    (LieModule.lowerCentralSeries R F F k).toSubmodule =
      DirectSum.degreeTail (homogeneousSubmodule R S) (fun n => (n : ℤ)) (k + 1) := by
  rw [lowerCentralSeries_toSubmodule_eq_span_words]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw
    exact DirectSum.le_degreeTail (homogeneousSubmodule R S) (fun n => (n : ℤ))
      (by omega : ((k + 1 : ℕ) : ℤ) ≤ (w.length : ℤ)) (word_mem_homogeneousSubmodule R w)
  · rw [DirectSum.degreeTail_def]
    refine iSup_le fun n => iSup_le fun hn => ?_
    rw [homogeneousSubmodule_def]
    apply Submodule.span_mono
    apply Set.image_mono
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    omega

/-- The lower central series of a free Lie algebra is separated over every
commutative ring. -/
theorem iInf_lowerCentralSeries_eq_bot :
    (⨅ k : ℕ, LieModule.lowerCentralSeries R F F k) = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule]
  apply le_antisymm _ bot_le
  have hle :
      (⨅ k : ℕ, (LieModule.lowerCentralSeries R F F k).toSubmodule) ≤
        ⨅ k : ℕ, DirectSum.degreeTail (homogeneousSubmodule R S) (fun n => (n : ℤ)) k := by
    apply le_iInf
    intro k x hx
    have hk := (iInf_le (fun k => (LieModule.lowerCentralSeries R F F k).toSubmodule) k) hx
    rw [lowerCentralSeries_toSubmodule_eq_degreeTail] at hk
    exact DirectSum.degreeTail_antitone (homogeneousSubmodule R S) (fun n => (n : ℤ))
      (Nat.le_succ k) hk
  rwa [DirectSum.iInf_degreeTail_eq_bot] at hle

end Mei.FreeLieAlgebra
