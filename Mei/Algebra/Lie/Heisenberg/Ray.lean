/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Heisenberg.Grading
public import Mei.Algebra.Lie.Graded.Ray

/-!
# The Heisenberg grading does not have abelian rays

For the grading of the Heisenberg Lie algebra over `ℤ` with `X` and `Y` in degree one and `Z`
in degree two (`heisenbergGrading`), `X` and `Y` lie on the supported ray through degree one of
the nonnegative integers. Since `⁅X, Y⁆ = Z` is nonzero over a nontrivial coefficient ring, this
grading fails `IsAbelianRays` (`not_isAbelianRays_heisenbergGrading`), so the results stated
under `IsAbelianRays`, such as the commutation of labels in one completed ray group, do not
apply to it.

The proof applies `isAbelianRays_iff` to the supported ray through `1`, obtained from
`PositiveDegrees.exists_supportedRay`, and uses Tau Ceti's `lie_heisenbergX_heisenbergY` and
`heisenbergZ_ne_zero`. This is the Heisenberg check of the abelian-ray condition of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2).
-/

public section

namespace Mei

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- Over a nontrivial coefficient ring, the Heisenberg grading by the nonnegative integers does
not have abelian rays: `X` and `Y` lie in degree one on the supported ray through `1`, and
their bracket `Z` is nonzero. -/
theorem not_isAbelianRays_heisenbergGrading [Nontrivial R] :
    ¬ IsAbelianRays PositiveDegrees.nonnegIntegers (heisenbergGrading R) := by
  intro h
  obtain ⟨w, hw⟩ := PositiveDegrees.nonnegIntegers.exists_supportedRay
    (PositiveDegrees.mem_nonnegIntegers_monoid.mpr zero_le_one) one_ne_zero
  apply heisenbergZ_ne_zero (R := R)
  rw [← lie_heisenbergX_heisenbergY]
  exact (isAbelianRays_iff (heisenbergGrading R)).mp h w 1 1 hw hw _
    (heisenbergX_mem_grading R) _ (heisenbergY_mem_grading R)

end Mei
