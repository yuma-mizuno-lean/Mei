/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Realization
public import Mei.Geometry.ScatteringDiagram.Skew.LieAlgebra
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom

/-!
# The graded principal Lie embedding

The principal realization of a skew lattice datum is a Lie homomorphism. On the
positive skew algebra over a free ambient lattice it is injective, and carries
degree `n` to the principal degree `r(n) = (p₁*(n), n)` with the same cutoff order.
Thus it supplies the graded map required to transport nilpotent truncations and
completed BCH labels into the
tropical vertex algebra. Injectivity requires no nondegeneracy of the skew form:
the retained unfrozen coordinate distinguishes even radical exponents, while the
principal normal detects their coefficients over a free ambient lattice.

The construction reuses `principalRealization`, its coefficient recovery, and
`SkewLieAlgebra.positiveGrading`. The principal embedding follows
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N R : Type*} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  (D : SkewLatticeDatum N)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen
local notation "β" => D.coefficientForm R
local notation "hβ" => D.isAlt_coefficientForm R

/-- The principal realization as a Lie homomorphism on the ambient skew algebra.
Its degree-zero generator is killed; for a free ambient lattice its restriction to
positive degrees is faithful. -/
def principalLieHom : D.skewLieAlgebra R →ₗ⁅R⁆
    LogarithmicVectorField R Lpr Lpr (AddMonoidHom.id Lpr) :=
  { (D.principalRealization (R := R)).comp (SkewLieAlgebra.toFinsupp β hβ).toLinearMap with
    map_lie' := by
      intro x y
      simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap]
      induction x using SkewLieAlgebra.induction_on β hβ with
      | h0 => simp
      | hs n r =>
        induction y using SkewLieAlgebra.induction_on β hβ with
        | h0 => simp
        | hs m s =>
          simp only [SkewLieAlgebra.single_bracket_single, SkewLieAlgebra.toFinsupp_single,
            principalRealization_single, smul_lie, lie_smul, lie_principalField,
            coefficientForm_apply, smul_smul, mul_assoc, mul_left_comm]
        | ha y z hy hz => simp_all
      | ha x z hx hz => simp_all }

/-- The ambient principal Lie map uses the existing linear realization of coefficients. -/
theorem principalLieHom_apply (x : D.skewLieAlgebra R) :
    D.principalLieHom x = D.principalRealization (SkewLieAlgebra.toFinsupp β hβ x) := (rfl)

/-- A skew generator maps to the corresponding scalar multiple of its principal field. -/
@[simp]
theorem principalLieHom_single (n : D.unfrozen) (c : R) :
    D.principalLieHom (SkewLieAlgebra.single β hβ n c) = c • D.principalField n := by
  rw [principalLieHom_apply, SkewLieAlgebra.toFinsupp_single, principalRealization_single]

variable (d : PositiveDegrees D.unfrozen)

local notation "𝔤" => SkewLieAlgebra.positiveLieAlgebra β hβ d
local notation "ℒ" => SkewLieAlgebra.positiveGrading β hβ d
local notation "ℳ" => tropicalVertexGrading
  (R := R) (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr)

private theorem principalLieHom_mem (x : 𝔤) :
    D.principalLieHom x.val ∈ tropicalVertexLieAlgebra
      (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) := by
  rw [principalLieHom_apply]
  apply D.principalRealization_mem_tropicalVertexLieAlgebra d
  intro n hn
  by_contra h
  exact (Finsupp.mem_support_iff.mp hn)
    ((SkewLieAlgebra.mem_positiveLieAlgebra_iff β hβ d x.val).mp x.property n (Or.inl h))

/-- The principal Lie map on the positive subalgebra, with codomain restricted to the
tropical vertex Lie algebra. -/
private def principalPositiveLieHom :
    𝔤 →ₗ⁅R⁆ tropicalVertexLieAlgebra (R := R)
      (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr) :=
  { ((D.principalLieHom (R := R)).toLinearMap.comp
      (SkewLieAlgebra.positiveLieAlgebra β hβ d).incl.toLinearMap).codRestrict
        _ (D.principalLieHom_mem d) with
    map_lie' {x y} := Subtype.ext (D.principalLieHom.map_lie x.val y.val) }

private theorem coe_principalPositiveLieHom_apply (x : 𝔤) :
    (D.principalPositiveLieHom (R := R) d x).val = D.principalLieHom x.val := (rfl)

/-- The principal embedding of the positive skew Lie algebra into the tropical
vertex Lie algebra. Its degree map is graph inclusion, with identity cutoff modulus. -/
def principalGradedLieHom :
    GradedLieHom (d.graphMap D.principalCharacter.toAddMonoidHom) ℒ ℳ where
  toLieHom := D.principalPositiveLieHom d
  map_mem {n x} hx := by
    obtain ⟨c, hc⟩ := (SkewLieAlgebra.mem_grade_iff β hβ n x.val).mp
      ((SkewLieAlgebra.mem_positiveGrading_iff β hβ d n x).mp hx)
    apply (mem_tropicalVertexGrading_iff _ _ _ _).mpr
    refine ⟨c • D.principalEvaluation n, ?_⟩
    rw [coe_principalPositiveLieHom_apply, ← hc, principalLieHom_single]
    apply (LogarithmicVectorField.toFinsupp _).injective
    simp

/-- Forgetting the target positive subalgebra recovers the ambient principal map. -/
@[simp]
theorem coe_principalGradedLieHom_apply (x : 𝔤) :
    (D.principalGradedLieHom (R := R) d x).val = D.principalLieHom x.val :=
  D.coe_principalPositiveLieHom_apply d x

/-- The principal graded realization is injective, including for a zero skew form
and rational coefficient algebras with zero divisors. -/
theorem principalGradedLieHom_injective [Module.Free ℤ N] :
    Function.Injective (D.principalGradedLieHom (R := R) d) := by
  apply (injective_iff_map_eq_zero (D.principalGradedLieHom d)).mpr
  intro x hx
  have hz : D.principalRealization (SkewLieAlgebra.toFinsupp β hβ x.val) = 0 := by
    simpa only [coe_principalGradedLieHom_apply, principalLieHom_apply, ZeroMemClass.coe_zero]
      using congrArg Subtype.val hx
  have hc := (D.principalRealization_eq_zero_iff _).mp hz
  have h0 := (SkewLieAlgebra.mem_positiveLieAlgebra_iff β hβ d x.val).mp x.property
    0 (Or.inr rfl)
  rw [h0, Finsupp.single_zero] at hc
  apply Subtype.ext
  exact (SkewLieAlgebra.toFinsupp β hβ).injective (hc.trans (map_zero _).symm)

end Mei.SkewLatticeDatum
