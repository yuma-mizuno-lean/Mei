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
