/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.Constant
public import Mei.Geometry.ScatteringDiagram.WallSpace.Shifted.DirectLimit

/-!
# Constant sections of zero spatial direction under ordinary walls

Completed BCH labels act linearly on the global shifted coefficients, so a finite wall diagram
labelled in the completed BCH group has a coefficient local system with values in them. The
zero-direction coefficients are the span of the finite homogeneous coefficients, in all charts,
whose degree `r` satisfies `ρ r = 0`. Every ordinary wall label fixes them. Hence for a diagram
all of whose labels lie in wall groups, these coefficients are constant sections of the
coefficient local system over every open subset of the regular locus, uniquely determined by
their values, and linear in the coefficient.

No global consistency of the diagram, finiteness of the labels' logarithms or spanning
assumption on the positive monoid is used. The statements specialize
`FiniteWallDiagram.constantCoefficientSections` to the completed BCH action, whose fixed
coefficients are the zero-direction case of
`DirectedWallSpaces.shiftedDirectLimitBCHAction_of_eq_self_of_direction_eq_zero`. The
zero-direction convention follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §2.1 and §3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

open TopologicalSpace Opposite

namespace Mei

namespace PositiveDegrees

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (ℳ : Γ → Submodule R M)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]

omit [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M] [DirectSum.Decomposition ℳ] in
/-- The global coefficients spanned by the finite homogeneous coefficients of zero spatial
direction, taken in every chart: those lying in a degree `r` with `ρ r = 0`. -/
def zeroDirectionCoefficients : Submodule R (d.ShiftedDirectLimit ℳ) :=
  Submodule.span R {x | ∃ (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (r : Γ) (a : shiftedSubmodule ℳ d.monoid p),
      (a : M) ∈ ℳ r ∧ ρ r = 0 ∧
        x = d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a)}

omit [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M] [DirectSum.Decomposition ℳ] in
/-- A finite homogeneous coefficient of zero spatial direction, in any containing chart, is a
zero-direction coefficient. -/
theorem toShiftedDirectLimitOfChart_mem_zeroDirectionCoefficients (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid) {r : Γ}
    (hr : ρ r = 0) (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) :
    d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a) ∈
      d.zeroDirectionCoefficients ρ ℳ :=
  Submodule.subset_span ⟨p, s, hp, r, a, ha, hr, rfl⟩

/-- Completed BCH labels act additively on the global shifted coefficients. -/
instance instDistribMulActionShiftedDirectLimit :
    DistribMulAction (d.completedBCHGroup ℒ) (d.ShiftedDirectLimit ℳ) :=
  DistribMulAction.compHom _ (d.shiftedDirectLimitBCHAction ℒ ℳ)

/-- The completed BCH action commutes with the coefficient scalars. -/
instance instSMulCommClassShiftedDirectLimit :
    SMulCommClass (d.completedBCHGroup ℒ) R (d.ShiftedDirectLimit ℳ) :=
  SMul.comp.smulCommClass (β := R) (d.shiftedDirectLimitBCHAction ℒ ℳ)

/-- The scalar action of a completed label is the global BCH action. -/
@[simp]
theorem smul_eq_shiftedDirectLimitBCHAction (g : d.completedBCHGroup ℒ)
    (x : d.ShiftedDirectLimit ℳ) : g • x = d.shiftedDirectLimitBCHAction ℒ ℳ g x := (rfl)

end PositiveDegrees

namespace DirectedWallSpaces

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] [IsWallAnnihilating H ℳ]

/-- Ordinary wall labels fix every zero-direction coefficient. -/
theorem smul_eq_self_of_mem_zeroDirectionCoefficients
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) {x : d.ShiftedDirectLimit ℳ}
    (hx : x ∈ d.zeroDirectionCoefficients ρ ℳ) : g • x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, s, hp, r, a, ha, hr, rfl⟩ := hx
    rw [PositiveDegrees.smul_eq_shiftedDirectLimitBCHAction]
    exact H.shiftedDirectLimitBCHAction_of_eq_self_of_direction_eq_zero ℳ p s hp hg a ha hr
  | zero => exact smul_zero g
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | smul r x _ hx => rw [smul_comm, hx]

end DirectedWallSpaces

namespace FiniteWallDiagram

variable {N V Γ Λ R L M : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [AddCommGroup Γ] [AddCommMonoid Λ] [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [LieModule R L M] [DecidableEq Γ] {ρ : Γ →+ Λ} {d : PositiveDegrees Γ}
  {ℒ : Γ → Submodule R L} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] [IsWallAnnihilating H ℳ]
  (D : FiniteWallDiagram C (d.completedBCHGroup ℒ))
  (hD : ∀ P, ∃ (w : SupportedRay d) (m : Λ →+ ℤ), D.label P ∈ H.wallGroup w m)
  (U : Opens C.regularSpace)

include hD in
/-- Over a finite wall diagram all of whose labels are ordinary wall labels, the zero-direction
coefficients are constant sections of the coefficient local system over every open subset of the
regular locus: there is a unique linear map into the sections whose value at each off-wall point
is the coefficient itself. -/
theorem existsUnique_coefficientSections_eq_of_mem_zeroDirectionCoefficients :
    ∃! t : d.zeroDirectionCoefficients ρ ℳ →ₗ[R]
        (D.coefficientLocalSystem (d.ShiftedDirectLimit ℳ)).presheaf.obj (op U),
      ∀ (x : d.zeroDirectionCoefficients ρ ℳ) (y : C.coefficientPoints) (hy : y.val ∈ U),
        (D.coefficientTransport (d.ShiftedDirectLimit ℳ)).value (t x) y hy = x := by
  have hfix (x : d.zeroDirectionCoefficients ρ ℳ) (P : C.walls) :
      D.label P • (x : d.ShiftedDirectLimit ℳ) = x := by
    obtain ⟨w, m, hP⟩ := hD P
    exact H.smul_eq_self_of_mem_zeroDirectionCoefficients ℳ hP x.property
  refine ⟨D.constantCoefficientSections _ U (d.zeroDirectionCoefficients ρ ℳ).subtype hfix,
    fun x y hy => D.value_constantCoefficientSections _ U _ hfix x y hy, fun t ht => ?_⟩
  exact D.eq_constantCoefficientSections_of_value_eq _ U _ hfix ht

end FiniteWallDiagram

end Mei
