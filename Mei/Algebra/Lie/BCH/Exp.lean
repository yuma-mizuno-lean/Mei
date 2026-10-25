/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Group
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Integrating Lie maps into nilpotent associative ideals

A rational Lie homomorphism with image in a nilpotent associative ideal integrates
to a homomorphism from the BCH group into the units of the associative algebra.
Its values are finite exponentials. Finite logarithms recover the original Lie map,
so integration preserves and reflects injectivity. Both precomposition by Lie maps
and postcomposition by algebra maps commute with integration.

This uses `Mei.exp_map_bchOfClass` to compare the universal BCH polynomial with
associative exponentials, and Tau Ceti's `nilpotentExpUnit` and
`IsNilpotent.log_exp` for units and logarithmic coordinates. The ideal may be a
left ideal; no freeness or finite-dimensionality is required.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieHom

open Mei

variable {L L' A B : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing.IsNilpotent L] [LieRing L'] [LieAlgebra ℚ L']
  [LieRing.IsNilpotent L'] [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

/-- Finite exponentials turn BCH into multiplication whenever the representation
takes values in a nilpotent associative ideal. -/
theorem exp_map_bch (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) (x y : L) :
    IsNilpotent.exp (f (bch x y)) = IsNilpotent.exp (f x) * IsNilpotent.exp (f y) := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℚ L L
  obtain ⟨n, hn⟩ := hI
  let k := max c n
  have hk : LieModule.lowerCentralSeries ℚ L L k = ⊥ :=
    eq_bot_iff.mpr ((LieModule.antitone_lowerCentralSeries ℚ L L (le_max_left c n)).trans hc.le)
  have hIk : I ^ (k + 1) = ⊥ := by
    apply eq_bot_iff.mpr
    exact (Ideal.pow_le_pow_right (by omega : n ≤ k + 1)).trans (by simpa using hn.le)
  rw [bch_eq_bchOfClass k hk]
  exact exp_map_bchOfClass k hk f I hIk hf x y

/-- Integrate a representation into a nilpotent associative ideal by finite exponentials. -/
noncomputable def bchExpHom (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) : BCHGroup L →* Aˣ where
  toFun g := TauCeti.nilpotentExpUnit (I.isNilpotent_of_mem hI (hf (BCHGroup.log g)))
  map_one' := by
    apply Units.ext
    simp [IsNilpotent.exp_zero]
  map_mul' g h := by
    apply Units.ext
    simpa only [TauCeti.coe_nilpotentExpUnit, Units.val_mul, BCHGroup.log_mul] using
      f.exp_map_bch I hI hf (BCHGroup.log g) (BCHGroup.log h)

/-- The integrated homomorphism is the finite exponential in logarithmic coordinates. -/
@[simp]
theorem coe_bchExpHom (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) (g : BCHGroup L) :
    (f.bchExpHom I hI hf g : A) = IsNilpotent.exp (f (BCHGroup.log g)) := by
  simp [bchExpHom]

/-- Taking the finite logarithm recovers the represented Lie coordinate. -/
@[simp↓]
theorem log_bchExpHom (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) (g : BCHGroup L) :
    IsNilpotent.log (f.bchExpHom I hI hf g : A) = f (BCHGroup.log g) := by
  rw [coe_bchExpHom]
  exact IsNilpotent.log_exp (I.isNilpotent_of_mem hI (hf _))

/-- Integration is faithful exactly when the Lie representation is faithful. -/
theorem bchExpHom_injective_iff (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) :
    Function.Injective (f.bchExpHom I hI hf) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    apply BCHGroup.exp.injective
    apply h
    apply Units.ext
    simp [hxy]
  · intro h g g' he
    apply BCHGroup.log_injective
    apply h
    simpa only [log_bchExpHom] using
      congrArg (fun u : Aˣ => IsNilpotent.log (u : A)) he

/-- Integration commutes with precomposition by a Lie homomorphism. -/
theorem bchExpHom_comp (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) (g : L' →ₗ⁅ℚ⁆ L) :
    (f.comp g).bchExpHom I hI (fun x => by
      simpa only [LieHom.comp_apply] using hf (g x)) =
      (f.bchExpHom I hI hf).comp g.bchGroupMap := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  rw [coe_bchExpHom (f.comp g)]
  simp

/-- Integration commutes with an algebra map carrying the represented image into
a nilpotent ideal of the target. -/
theorem map_bchExpHom (f : L →ₗ⁅ℚ⁆ A) (I : Ideal A) (hI : IsNilpotent I)
    (hf : ∀ x, f x ∈ I) (φ : A →ₐ[ℚ] B) (J : Ideal B) (hJ : IsNilpotent J)
    (hf' : ∀ x, (φ.toLieHom.comp f) x ∈ J) :
    (Units.map (φ : A →* B)).comp (f.bchExpHom I hI hf) =
      (φ.toLieHom.comp f).bchExpHom J hJ hf' := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  rw [coe_bchExpHom f, coe_bchExpHom (φ.toLieHom.comp f)]
  simpa only [LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.coe_toMonoidHom] using
    (I.isNilpotent_of_mem hI (hf (BCHGroup.log g))).map_exp φ

end LieHom
