/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.InnerAutomorphism

/-!
# Scalar independence of exponential adjoint automorphisms

The action of exponential adjoint automorphisms on vectors is independent of the
scalar ring used to form the adjoint endomorphism.

The imported `LieHom.map_expAd` intertwines these automorphisms with Lie
homomorphisms whenever both adjoint operators are nilpotent.
-/

public section

attribute [simp] LieHom.map_expAd

namespace Mei

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- Exponential adjoint automorphisms act identically for any two scalar structures
on the same rational Lie ring. No compatibility between the scalars is required. -/
theorem expAd_apply_eq_expAd (R S : Type*) [CommRing R] [CommRing S]
    [LieAlgebra R L] [LieAlgebra S L] (x y : L)
    (hR : IsNilpotent (LieAlgebra.ad R L x))
    (hS : IsNilpotent (LieAlgebra.ad S L x)) :
    TauCeti.expAd x hR.exists_pow_apply_eq_zero y =
      TauCeti.expAd x hS.exists_pow_apply_eq_zero y := by
  have hp (n : ℕ) (z : L) :
      (LieAlgebra.ad R L x ^ n) z = (LieAlgebra.ad S L x ^ n) z := by
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', mul_apply_eq_comp, LieAlgebra.ad_apply, ih]
  obtain ⟨n, hy⟩ := hR.exists_pow_apply_eq_zero y
  rw [TauCeti.expAd_apply_eq_sum hR.exists_pow_apply_eq_zero hy,
    TauCeti.expAd_apply_eq_sum hS.exists_pow_apply_eq_zero (hp n y ▸ hy)]
  simp only [hp]

end Mei
