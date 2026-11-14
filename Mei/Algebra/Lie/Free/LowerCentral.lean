/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Free.LowerCentral
public import TauCeti.Algebra.Lie.LowerCentralSeries
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.DirectSum.DegreeTail

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

open TauCeti.FreeLieAlgebra

namespace Mei.FreeLieAlgebra

variable (R : Type*) [CommRing R] {S : Type*}

local notation "F" => _root_.FreeLieAlgebra R S

-- Supply the endomorphism Lie ring required by `LieAlgebra.ad`.
attribute [local instance] LieRing.ofAssociativeRing

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

/-- The lower central series of a free Lie algebra is separated over every
commutative ring. -/
theorem iInf_lowerCentralSeries_eq_bot :
    (⨅ k : ℕ, LieModule.lowerCentralSeries R F F k) = ⊥ := by
  apply LieSubmodule.toSubmodule_injective
  rw [LieSubmodule.iInf_toSubmodule, LieSubmodule.bot_toSubmodule]
  apply le_antisymm _ bot_le
  have hle :
      (⨅ k : ℕ, (LieModule.lowerCentralSeries R F F k).toSubmodule) ≤
        ⨅ k : ℕ, TauCeti.DirectSum.degreeTail (homogeneousSubmodule R S) (fun n => (n : ℤ)) k := by
    apply le_iInf
    intro k x hx
    have hk := (iInf_le (fun k => (LieModule.lowerCentralSeries R F F k).toSubmodule) k) hx
    rw [← TauCeti.FreeLieAlgebra.degreeTail_eq_lowerCentralSeries] at hk
    exact TauCeti.DirectSum.degreeTail_antitone (homogeneousSubmodule R S) (fun n => (n : ℤ))
      (Nat.le_succ k) hk
  rwa [TauCeti.DirectSum.iInf_degreeTail_eq_bot] at hle

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

/-- A homomorphism from the free lower-central quotient is the induced lift if
it agrees with the given map on the quotient generators. -/
theorem liftLowerCentralQuotient_unique (c : ℕ)
    (hc : LieModule.lowerCentralSeries R L L c = ⊥) (f : S → L)
    (g : F ⧸ LieModule.lowerCentralSeries R F F c →ₗ⁅R⁆ L)
    (h : ∀ s, g (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of R s)) = f s) :
    g = liftLowerCentralQuotient R c hc f := by
  have he : g.comp (LieIdeal.mkQ (LieModule.lowerCentralSeries R F F c)) =
      _root_.FreeLieAlgebra.lift R f :=
    (_root_.FreeLieAlgebra.lift_unique f _).mp (funext h)
  apply LieIdeal.lieHom_qext (LieModule.lowerCentralSeries R F F c)
  intro z
  simpa only [LieHom.comp_apply, LieIdeal.mkQ_apply, liftLowerCentralQuotient_mk] using
    LieHom.congr_fun he z

end Mei.FreeLieAlgebra
