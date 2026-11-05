/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital
public import Mei.RingTheory.GradedAlgebra.Supported

/-!
# The unit of global shifted coefficients

When the original algebra unit is homogeneous in degree zero, its image is a unit
for global coefficient multiplication. The resulting ring and algebra retain the original
direct-limit additive group and scalar multiplication.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMonoid 𝒜]

private def shiftedOne : shiftedSubmodule 𝒜 d.monoid 0 :=
  ⟨1, by
    have h : (1 : A) ∈ (supportedSubalgebra 𝒜 d.monoid).toSubmodule :=
      (supportedSubalgebra 𝒜 d.monoid).one_mem
    rwa [supportedSubalgebra_toSubmodule] at h⟩

omit [DecidableEq Γ] [DirectSum.Decomposition 𝒜] in
private theorem coe_shiftedOne : (d.shiftedOne 𝒜 : A) = 1 := (rfl)

private theorem shiftedHomogeneousComponent_unit_products (p u : Γ)
    (x : d.ShiftedCoefficients 𝒜 p) :
    d.shiftedHomogeneousComponent 𝒜 (0 + p) u
        (d.shiftedCompletionMul 𝒜 0 p ((d.shiftedFiltration 𝒜 0).of (d.shiftedOne 𝒜)) x) =
      d.shiftedHomogeneousComponent 𝒜 p u x ∧
    d.shiftedHomogeneousComponent 𝒜 (p + 0) u
        (d.shiftedCompletionMul 𝒜 p 0 x ((d.shiftedFiltration 𝒜 0).of (d.shiftedOne 𝒜))) =
      d.shiftedHomogeneousComponent 𝒜 p u x := by
  let k := (d.degree (u - p)).toNat
  have hk : d.degree (u - p) ≤ k := Int.self_le_toNat _
  obtain ⟨v, hv⟩ := ((d.shiftedFiltration 𝒜 p).submodule (k + 1)).mkQ_surjective
    ((d.shiftedFiltration 𝒜 p).projection k x)
  have h1 := ((d.shiftedFiltration 𝒜 0).projection_of k (d.shiftedOne 𝒜)).symm
  constructor
  · have hk' : d.degree (u - (0 + p)) ≤ k := by simpa only [zero_add] using hk
    rw [d.shiftedHomogeneousComponent_eq 𝒜 (0 + p) u k hk',
      d.projection_shiftedCompletionMul 𝒜 0 p k _ x (d.shiftedOne 𝒜) v h1 hv,
      shiftedQuotientComponent_mk, d.shiftedHomogeneousComponent_eq 𝒜 p u k hk,
      ← hv, Submodule.mkQ_apply, shiftedQuotientComponent_mk]
    apply Subtype.ext
    simp only [coe_shiftedMul, coe_shiftedOne, one_mul]
  · have hk' : d.degree (u - (p + 0)) ≤ k := by simpa only [add_zero] using hk
    rw [d.shiftedHomogeneousComponent_eq 𝒜 (p + 0) u k hk',
      d.projection_shiftedCompletionMul 𝒜 p 0 k x _ v (d.shiftedOne 𝒜) hv h1,
      shiftedQuotientComponent_mk, d.shiftedHomogeneousComponent_eq 𝒜 p u k hk,
      ← hv, Submodule.mkQ_apply, shiftedQuotientComponent_mk]
    apply Subtype.ext
    simp only [coe_shiftedMul, coe_shiftedOne, mul_one]

/-- The image of the original algebra unit in the chart indexed by the empty multiset (origin 0). -/
def shiftedDirectLimitOne : d.ShiftedDirectLimit 𝒜 :=
  d.toShiftedDirectLimitOfChart 𝒜 0 0 d.zero_coefficientOrigin_mem
    ((d.shiftedFiltration 𝒜 0).of (d.shiftedOne 𝒜))

/-- The original degree-zero unit acts as a left unit on every global coefficient. -/
theorem shiftedDirectLimitOne_mul (x : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 (d.shiftedDirectLimitOne 𝒜) x = x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [shiftedDirectLimitOne, toShiftedDirectLimit_eq_ofChart,
    shiftedDirectLimitMul_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact (d.shiftedHomogeneousComponent_unit_products 𝒜 (d.coefficientOrigin s) u a).1

/-- The original degree-zero unit acts as a right unit on every global coefficient. -/
theorem shiftedDirectLimitMul_one (x : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 x (d.shiftedDirectLimitOne 𝒜) = x := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  apply d.shiftedDirectLimitComponents_injective 𝒜
  funext u
  rw [shiftedDirectLimitOne, toShiftedDirectLimit_eq_ofChart,
    shiftedDirectLimitMul_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact (d.shiftedHomogeneousComponent_unit_products 𝒜 (d.coefficientOrigin s) u a).2

instance instRingShiftedDirectLimit : Ring (d.ShiftedDirectLimit 𝒜) where
  __ := (inferInstance : NonUnitalRing (d.ShiftedDirectLimit 𝒜))
  one := d.shiftedDirectLimitOne 𝒜
  one_mul := d.shiftedDirectLimitOne_mul 𝒜
  mul_one := d.shiftedDirectLimitMul_one 𝒜

/-- The ring unit is the image of the original degree-zero unit. -/
@[simp]
theorem shiftedDirectLimitOne_eq_one : d.shiftedDirectLimitOne 𝒜 = 1 := (rfl)

/-- The global unit has the same ambient components as the original algebra unit. -/
@[simp]
theorem shiftedDirectLimitComponents_one (u : Γ) :
    d.shiftedDirectLimitComponents 𝒜 (1 : d.ShiftedDirectLimit 𝒜) u =
      DirectSum.decompose 𝒜 (1 : A) u := by
  rw [← d.shiftedDirectLimitOne_eq_one 𝒜, shiftedDirectLimitOne,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart, shiftedHomogeneousComponent_of,
    coe_shiftedOne]

instance instAlgebraShiftedDirectLimit : Algebra R (d.ShiftedDirectLimit 𝒜) :=
  Algebra.ofModule (fun r x y => smul_assoc r x y) (fun r x y => (smul_comm r x y).symm)

end Mei.PositiveDegrees
