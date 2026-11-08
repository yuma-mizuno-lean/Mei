/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit

/-!
# Zero-direction components of global shifted coefficients

The zero-direction coefficients are the span of the finite homogeneous coefficients, in all
charts, whose degree `r` satisfies `ρ r = 0`. The convention follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §2.1 and §3.3.3
(arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ Λ R M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ] [CommRing R]
  [AddCommGroup M] [Module R M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (ℳ : Γ → Submodule R M)

/-- The global coefficients spanned by the finite homogeneous coefficients of zero spatial
direction, taken in every chart: those lying in a degree `r` with `ρ r = 0`. -/
def zeroDirectionCoefficients : Submodule R (d.ShiftedDirectLimit ℳ) :=
  Submodule.span R {x | ∃ (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (r : Γ) (a : shiftedSubmodule ℳ d.monoid p),
      (a : M) ∈ ℳ r ∧ ρ r = 0 ∧
        x = d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a)}

/-- The zero-direction coefficients are spanned by zero-direction homogeneous chart elements. -/
theorem zeroDirectionCoefficients_def :
    d.zeroDirectionCoefficients ρ ℳ =
      Submodule.span R {x | ∃ (p : Γ) (s : Multiset d.monoid)
        (hp : p - d.coefficientOrigin s ∈ d.monoid) (r : Γ)
        (a : shiftedSubmodule ℳ d.monoid p), (a : M) ∈ ℳ r ∧ ρ r = 0 ∧
          x = d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a)} := (rfl)

/-- A finite homogeneous coefficient of zero spatial direction, in any containing chart, is a
zero-direction coefficient. -/
theorem toShiftedDirectLimitOfChart_mem_zeroDirectionCoefficients (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid) {r : Γ}
    (hr : ρ r = 0) (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) :
    d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a) ∈
      d.zeroDirectionCoefficients ρ ℳ :=
  Submodule.subset_span ⟨p, s, hp, r, a, ha, hr, rfl⟩

end Mei.PositiveDegrees
