/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block
public import Mei.Algebra.Lie.Graded.Shifted.Operator.Block
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Operator

/-!
# Wall-event recursions on linear families

The canonical simultaneous-event operator acts on linear families of incoming
coefficients. Its homogeneous blocks are the differences of the existing
operator BCH actions and the identity, with the same normal-velocity condition
as the coefficient operator. Evaluation preserves the step and its finite
solution. Conversely, coefficient recursions for every input determine the
unique operator-valued solution.

The event sets and read points are the same in both operators. These results
apply after choosing them geometrically, without making that choice depend on
the incoming coefficient. No coefficient basis or finite-generation hypothesis
is imposed, and zero blocks and shifts invisible in space remain included.

The operator-probe interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
The construction uses `eventBlock`, `operatorBCHAction_lof_sub` and the shared
`shiftedOperatorLowerStep`, rather than a second component expansion.
-/

public noncomputable section

open scoped DirectSum
open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι A : Type*} {Γ : Type} {M L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommMonoid A] [Module R A]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)
  (k K : ℕ) (hkK : k ≤ K)
  (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
  (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V)

open Classical in
/-- The event endpoint step on linear incoming families, using the original
signed simultaneous-event blocks and the original normal-velocity condition. -/
def operatorEventEndpointStep :
    Module.End R (PositiveDegrees.ShiftedEndpointOperator (H := A) (V := V) d ℳ p k) :=
  PositiveDegrees.shiftedOperatorLowerStep d ℳ p k events
    (fun b n m _ =>
      if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
          b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
        eventBlock d ℳ p ℒ H h B k K hkK b n m
      else 0) point

local notation "U" => eventEndpointStep d ℳ p ℒ H h B k K hkK events point
local notation "Uop" => operatorEventEndpointStep (A := A) d ℳ p ℒ H h B k K hkK events point
local notation "ev" => PositiveDegrees.shiftedEndpointEval (H := A) (V := V) d ℳ p k
local notation "lof" m:max F:max =>
  DirectSum.lof R (d.cutoff k) (fun n : d.cutoff k => A →ₗ[R] ℳ (p + (n : Γ))) m F

/-- The event recurrence really uses the blocks of the operator BCH action.
The finite linear-map sum retains every strictly preceding component with
matching normal velocity, including zero components. -/
theorem operatorEventEndpointStep_apply
    (F : PositiveDegrees.ShiftedEndpointOperator (H := A) (V := V) d ℳ p k)
    (Q : V) (n : d.cutoff k) :
    Uop F Q n = ∑ b ∈ events Q n, ∑ m : d.cutoff k,
      if _hmn : d.Precedes m.val n.val then
        if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
            b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
          PositiveDegrees.operatorBCHAction d ℳ p ℒ k
              ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b))
              (lof m (F (point b Q n m) m)) n -
            (lof m (F (point b Q n m) m)) n
        else 0
      else 0 := by
  classical
  rw [operatorEventEndpointStep, PositiveDegrees.shiftedOperatorLowerStep_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp only [LinearMap.zero_comp]
  rw [PositiveDegrees.operatorBCHAction_lof_sub, eventBlock_def]

/-- Evaluation intertwines the linear-family event step with the existing
coefficient step for the same event sets and read points. -/
@[simp]
theorem shiftedEndpointEval_operatorEventEndpointStep (x : A)
    (F : PositiveDegrees.ShiftedEndpointOperator (H := A) (V := V) d ℳ p k) :
    ev x (Uop F) = U (ev x F) := by
  funext Q n
  rw [operatorEventEndpointStep,
    PositiveDegrees.shiftedEndpointEval_shiftedOperatorLowerStep,
    PositiveDegrees.shiftedLowerStep_apply, eventEndpointStep_apply]

/-- The linear-family event operator is nilpotent at the original cutoff. -/
theorem operatorEventEndpointStep_pow_eq_zero : Uop ^ (k + 1) = 0 :=
  PositiveDegrees.shiftedOperatorLowerStep_pow_eq_zero d ℳ p k events _ point

/-- Every input evaluates the finite operator solution to the finite solution
of the coefficient recurrence, without choosing a basis of the input module. -/
@[simp]
theorem shiftedEndpointEval_operatorEventEndpointStep_finiteRecursion (x : A)
    (source : PositiveDegrees.ShiftedEndpointOperator (H := A) (V := V) d ℳ p k) :
    ev x (Module.End.finiteRecursion Uop (k + 1) source) =
      Module.End.finiteRecursion U (k + 1) (ev x source) := by
  rw [operatorEventEndpointStep]
  refine (PositiveDegrees.shiftedEndpointEval_finiteRecursion
    d ℳ p k events _ point x source).trans ?_
  congr 2
  ext F Q n
  rw [PositiveDegrees.shiftedLowerStep_apply, eventEndpointStep_apply]

/-- Coefficient recursions for all incoming inputs characterize the single
linear-family solution. This applies separately to each independently proved
geometric recursion. -/
theorem eq_operatorEventEndpointStep_finiteRecursion_iff
    (source F : PositiveDegrees.ShiftedEndpointOperator (H := A) (V := V) d ℳ p k) :
    F = Module.End.finiteRecursion Uop (k + 1) source ↔
      ∀ x : A, ev x F = ev x source + U (ev x F) := by
  classical
  rw [operatorEventEndpointStep,
    PositiveDegrees.eq_finiteRecursion_iff_forall_eval_eq_add]
  apply forall_congr'
  intro x
  have he := shiftedEndpointEval_operatorEventEndpointStep
    d ℳ p ℒ H h B k K hkK events point x F
  rw [operatorEventEndpointStep,
    PositiveDegrees.shiftedEndpointEval_shiftedOperatorLowerStep] at he
  rw [he]

end Mei.ModuleProbe
