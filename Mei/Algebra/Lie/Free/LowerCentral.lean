/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Free.Grading
public import TauCeti.Algebra.Lie.LowerCentralSeries
public import TauCeti.Algebra.Lie.Quotient
public import Mei.Algebra.DirectSum.Degree.Basic

/-!
# Word length and the lower central series of a free Lie algebra

Mathlib numbers the lower central series from zero. Its `k`-th term in a
free Lie algebra is precisely the span of bracketed words with at least `k + 1`
leaves. This description holds over every commutative ring.

This identifies lower central quotients with word-length truncations, so their
elements can be studied through the homogeneous pieces of the free Lie algebra.
The universal map to a Lie algebra with a specified nilpotency bound descends to
the corresponding quotient, using `FreeLieAlgebra.lift` and `LieIdeal.liftQ`.

## References

* `TauCeti.lie_lowerCentralSeries_le`: bracket estimate for lower central terms.
-/

public section

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] {S : Type*}

local notation "F" => _root_.FreeLieAlgebra R S

-- Supply the endomorphism Lie ring required by `LieAlgebra.ad`.
attribute [local instance] LieRing.ofAssociativeRing

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
  refine LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (Submodule.span R (word R '' {w : FreeMagma S | k + l + 1 < w.length})) _ _
    (LieAlgebra.ad R F).toLinearMap ?_ x y hx hy
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  rw [LieHom.coe_toLinearMap, LieAlgebra.ad_apply, ← word_mul]
  exact Submodule.subset_span ⟨u * v, by
    simp only [Set.mem_ofPred_eq, FreeMagma.length] at hu hv ⊢
    omega, rfl⟩

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

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- A map from the free generators to a Lie algebra with lower-central bound `c`
extends to a Lie homomorphism from the corresponding free lower-central quotient. -/
noncomputable def liftLowerCentralQuotient (c : ℕ)
    (hc : LieModule.lowerCentralSeries R L L c = ⊥) (f : S → L) :
    F ⧸ LieModule.lowerCentralSeries R F F c →ₗ⁅R⁆ L :=
  LieIdeal.liftQ (LieModule.lowerCentralSeries R F F c) (_root_.FreeLieAlgebra.lift R f) (by
    apply LieIdeal.map_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    rw [← hc]
    exact LieIdeal.map_lowerCentralSeries_le c)

/-- The induced map on a free lower-central quotient evaluates representatives
by the free Lie algebra's universal map. -/
@[simp]
theorem liftLowerCentralQuotient_mk (c : ℕ)
    (hc : LieModule.lowerCentralSeries R L L c = ⊥) (f : S → L) (z : F) :
    liftLowerCentralQuotient R c hc f (LieSubmodule.Quotient.mk z) =
      _root_.FreeLieAlgebra.lift R f z := by
  simp [liftLowerCentralQuotient]

end Mei.FreeLieAlgebra
