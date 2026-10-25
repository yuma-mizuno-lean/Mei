/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.InnerAutomorphism

/-!
# Naturality of exponential adjoint automorphisms

Lie homomorphisms intertwine the exponential adjoint automorphisms whenever both
adjoint operators are nilpotent. This permits identities proved in free nilpotent
Lie algebras to be evaluated in arbitrary Lie algebras. Its action on vectors is
independent of the scalar ring used to form the adjoint endomorphism.

The construction uses `TauCeti.expAd` and Mathlib's
`Module.End.commute_exp_left_of_commute` for intertwining nilpotent exponentials.
-/

public section

namespace LieHom

variable {R L L' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L']

/-- Lie homomorphisms intertwine exponential adjoint automorphisms.
No global nilpotence or injectivity assumption is needed. -/
@[simp]
theorem map_expAd (f : L →ₗ⁅R⁆ L') (x y : L)
    (hx : IsNilpotent (LieAlgebra.ad R L x))
    (hfx : IsNilpotent (LieAlgebra.ad R L' (f x))) :
    f (TauCeti.expAd x hx y) = TauCeti.expAd (f x) hfx (f y) := by
  have h : (LieAlgebra.ad R L' (f x)).comp f.toLinearMap =
      f.toLinearMap.comp (LieAlgebra.ad R L x) := by
    ext z
    exact (f.map_lie x z).symm
  simpa only [TauCeti.expAd_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap] using
    (LinearMap.congr_fun (Module.End.commute_exp_left_of_commute hx hfx h) y).symm

end LieHom

namespace Mei

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- Exponential adjoint automorphisms act identically for any two scalar structures
on the same rational Lie ring. No compatibility between the scalars is required. -/
theorem expAd_apply_eq_expAd (R S : Type*) [CommRing R] [CommRing S]
    [LieAlgebra R L] [LieAlgebra S L] (x y : L)
    (hR : IsNilpotent (LieAlgebra.ad R L x))
    (hS : IsNilpotent (LieAlgebra.ad S L x)) :
    TauCeti.expAd x hR y = TauCeti.expAd x hS y := by
  have hp (n : ℕ) (z : L) :
      (LieAlgebra.ad R L x ^ n) z = (LieAlgebra.ad S L x ^ n) z := by
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ih]
  obtain ⟨n, hn⟩ := hR
  have hy : (LieAlgebra.ad R L x ^ n) y = 0 := by rw [hn]; simp
  rw [TauCeti.expAd_apply_eq_sum ⟨n, hn⟩ hy,
    TauCeti.expAd_apply_eq_sum hS (by rw [← hp n y]; exact hy)]
  simp only [hp]

end Mei
