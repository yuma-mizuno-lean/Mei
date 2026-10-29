/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Skew.Specialization
public import Mei.Algebra.Lie.Logarithmic.Specialization
public import Mei.Geometry.ScatteringDiagram.Skew.Embedding

/-!
# Coefficient naturality of the principal skew realization

Specializing coefficients of a skew lattice algebra commutes with its principal
realization as formal logarithmic fields. The rational principal evaluation
characters, and hence the integral normalizations of ray labels, specialize with
the coefficients even for degenerate forms and coefficient rings with zero divisors.

We combine `SkewLieAlgebra.coefficientMap` with the coefficient specialization of
`LogarithmicVectorField` and `SkewLatticeDatum.principalLieHom`. The principal
realization and its normalization follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 and Appendix B, arXiv:1411.1394v2.
-/

public section
noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R S : Type*} [AddCommGroup N] [CommRing R] [CommRing S]
  [Algebra ℚ R] [Algebra ℚ S] (D : SkewLatticeDatum N) (φ : R →ₐ[ℚ] S)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "ρ" => AddMonoidHom.id Lpr

/-- Principal realization commutes with coefficient specialization as an equality
of formal fields, without any faithfulness or nondegeneracy assumption. -/
theorem coefficientMap_principalLieHom (x : D.skewLieAlgebra R) :
    LogarithmicVectorField.coefficientMap ρ φ 1 (D.principalLieHom x) =
      D.principalLieHom
        (SkewLieAlgebra.coefficientMap (D.coefficientForm R) (D.isAlt_coefficientForm R)
          (D.coefficientForm S) (D.isAlt_coefficientForm S) φ
          (fun _ _ => by simp) x) := by
  induction x using SkewLieAlgebra.induction_on
    (D.coefficientForm R) (D.isAlt_coefficientForm R) with
  | h0 => simp
  | hs n c =>
    apply LogarithmicVectorField.ext
    intro j
    ext q
    simp only [principalLieHom_single, SkewLieAlgebra.coefficientMap_single,
      LogarithmicVectorField.toFinsupp_coefficientMap, map_smul, toFinsupp_principalField,
      Finsupp.smul_single, MonoidHom.one_apply, one_smul]
    by_cases hj : (D.principalCharacter n, n) = j
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne (Ne.symm hj)]
  | ha x y hx hy => simp [hx, hy]

end Mei.SkewLatticeDatum
