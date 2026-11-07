/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Correction
public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component

/-!
# Degree changes of completed BCH actions on global shifted coefficients

A completed BCH label acts on the global shifted coefficients of a graded module, and
the action only raises ambient degree. In every translated chart containing a coefficient it
fixes the leading component, and it fixes the component of a homogeneous input in its own
degree. A homogeneous input has no output component outside its positive translate, and every
surviving output component in another degree strictly raises the relative degree. For an
arbitrary coefficient, the output component of relative degree `k + 1` is the input component
plus the same component of the images of the strictly lower input components.

These are the global forms of the statements for individual completed shifted coefficients.
They need no wall, annihilation or projection hypothesis and apply to arbitrary completed
labels acting on arbitrary graded Lie modules.
The unchanged-degree and degree-raising conventions follow Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 and Definition 2.10
([arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5)).
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]

/-- In every chart containing it, a global coefficient keeps its leading component under
every completed BCH label. -/
@[simp]
theorem shiftedDirectLimitComponents_BCHAction_toShiftedDirectLimitOfChart_origin
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (g : d.completedBCHGroup ℒ) (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedDirectLimitComponents ℳ
        (d.shiftedDirectLimitBCHAction ℒ ℳ g (d.toShiftedDirectLimitOfChart ℳ p s hp x)) p =
      d.shiftedHomogeneousComponent ℳ p p x := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    shiftedHomogeneousComponent_completedBCHAction]

/-- A global coefficient supported in the translate of `r` has image supported there. The
chart origin `p` may be strictly below `r`. -/
theorem shiftedDirectLimitComponents_BCHAction_eq_zero_of_support
    (p r : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ) (x : d.ShiftedCoefficients ℳ p)
    (hx : ∀ q, q - r ∉ d.monoid → d.shiftedHomogeneousComponent ℳ p q x = 0)
    {q : Γ} (hq : q - r ∉ d.monoid) :
    d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g (d.toShiftedDirectLimitOfChart ℳ p s hp x)) q = 0 := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact d.shiftedHomogeneousComponent_completedBCHAction_eq_zero_of_support ℒ ℳ r p hrp g x hx hq

/-- A homogeneous finite input has no output component outside its positive translate,
in any chart containing it. -/
theorem shiftedDirectLimitComponents_BCHAction_of_mem_eq_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {r q : Γ} (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) (hq : q - r ∉ d.monoid) :
    d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g
        (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a))) q = 0 := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact d.shiftedHomogeneousComponent_completedBCHAction_of_mem_eq_zero ℒ ℳ p hrp g a ha hq

/-- The component of a homogeneous finite input in its own degree is unchanged by every
completed BCH label, including when the input has positive relative order. -/
@[simp]
theorem shiftedDirectLimitComponents_BCHAction_of_mem_same
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {r : Γ} (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r) :
    d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g
        (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a))) r =
      ⟨a, ha⟩ := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart]
  exact d.shiftedHomogeneousComponent_completedBCHAction_of_mem_same ℒ ℳ p hrp g a ha

/-- Every surviving output component of a homogeneous finite input differs from the input
degree by a positive shift. This holds for every completed label, so also for inverses. -/
theorem sub_mem_monoid_of_shiftedDirectLimitComponents_BCHAction_ne_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {r q : Γ} (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r)
    (hq : d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g
        (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a))) q ≠ 0) :
    q - r ∈ d.monoid := by
  by_contra h
  exact hq (d.shiftedDirectLimitComponents_BCHAction_of_mem_eq_zero ℒ ℳ p s hp hrp g a ha h)

/-- A surviving output component of a homogeneous finite input in a different degree
strictly raises relative order, measured from any chart origin below the input degree. -/
theorem degree_lt_of_shiftedDirectLimitComponents_BCHAction_ne_zero
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    {r q : Γ} (hrp : r - p ∈ d.monoid) (hrq : r ≠ q) (g : d.completedBCHGroup ℒ)
    (a : shiftedSubmodule ℳ d.monoid p) (ha : (a : M) ∈ ℳ r)
    (hq : d.shiftedDirectLimitComponents ℳ
      (d.shiftedDirectLimitBCHAction ℒ ℳ g
        (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of a))) q ≠ 0) :
    d.degree (r - p) < d.degree (q - p) := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart] at hq
  exact d.degree_lt_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero ℒ ℳ p hrp hrq g
    a ha hq

/-- A transported global component of relative degree `k + 1` is the original component
plus contributions from strictly lower input degrees. Each contribution is the same
component of the transported homogeneous finite coefficient formed by one lower input
component, so the formula reads in the global coefficient module and holds in every chart
containing the input. -/
theorem shiftedDirectLimitComponents_BCHAction_eq_add_sum
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (g : d.completedBCHGroup ℒ) (x : d.ShiftedCoefficients ℳ p) (q : Γ) (k : ℕ)
    (hq : d.degree (q - p) = k + 1) :
    d.shiftedDirectLimitComponents ℳ
        (d.shiftedDirectLimitBCHAction ℒ ℳ g (d.toShiftedDirectLimitOfChart ℳ p s hp x)) q =
      d.shiftedHomogeneousComponent ℳ p q x +
        ∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          d.shiftedDirectLimitComponents ℳ
            (d.shiftedDirectLimitBCHAction ℒ ℳ g
              (d.toShiftedDirectLimitOfChart ℳ p s hp ((d.shiftedFiltration ℳ p).of
                (shiftedInclusion ℳ d.monoid p
                  ⟨n.val, (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
                  (d.shiftedHomogeneousComponent ℳ p (p + n.val) x))))) q := by
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    d.shiftedHomogeneousComponent_completedBCHAction_eq_add_sum ℒ ℳ p g x q k hq]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [shiftedDirectLimitBCHAction_toShiftedDirectLimitOfChart,
    shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    d.shiftedHomogeneousComponent_eq ℳ p q (k + 1) (by omega),
    (d.shiftedLieFiltration ℒ ℳ p).projection_completedBCHAction d ℒ g,
    ModuleFiltration.projection_of]

end Mei.PositiveDegrees
