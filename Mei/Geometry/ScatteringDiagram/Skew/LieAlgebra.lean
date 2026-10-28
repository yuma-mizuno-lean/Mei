/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.Algebra.Lie.Skew.Grading

/-!
# The Lie algebra of a skew lattice datum

A rational skew lattice form gives a coefficient-valued alternating form on the
unfrozen lattice over every commutative rational algebra. Its skew Lie algebra
retains a free generator at every unfrozen exponent, including radical degrees.
The generic positive grading and abelian-ray instances apply to any positive
monoid on this lattice; no adapted basis or nondegeneracy is required.

The bracket convention is `[X_n, X_m] = {m,n} X_(n+m)`, as in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2. The construction specializes
`Mei.SkewLieAlgebra` rather than identifying generators with their possibly
nonfaithful Poisson action.
-/

public section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] (D : SkewLatticeDatum N)
  (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The rational skew form, restricted to unfrozen exponents and mapped to coefficients. -/
def coefficientForm : D.unfrozen →ₗ[ℤ] D.unfrozen →ₗ[ℤ] R :=
  LinearMap.mk₂ ℤ (fun n m => algebraMap ℚ R (D.form n m))
    (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp)

@[simp]
theorem coefficientForm_apply (n m : D.unfrozen) :
    D.coefficientForm R n m = algebraMap ℚ R (D.form n m) := (rfl)

/-- Scalar extension of the rational skew form remains alternating. -/
theorem isAlt_coefficientForm : (D.coefficientForm R).IsAlt := by
  intro n
  simp

/-- The formal skew Lie algebra of the unfrozen lattice over the coefficient algebra.
Its positive part is `SkewLieAlgebra.positiveLieAlgebra` for the chosen positive degrees. -/
abbrev skewLieAlgebra := SkewLieAlgebra (D.coefficientForm R) (D.isAlt_coefficientForm R)

end Mei.SkewLatticeDatum
