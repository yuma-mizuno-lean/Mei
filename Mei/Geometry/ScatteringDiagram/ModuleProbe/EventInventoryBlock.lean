/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Block
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation

/-!
# Wall-event blocks for lower-degree steps

`eventBlock` is the coefficient of the difference between the truncated BCH
action of a simultaneous wall event's label and the identity, between two
retained relative degrees. It is obtained from the generic `labelBlock` by
truncating the label supplied by the directed diagram.

`eventEndpointStep` uses these coefficients, retaining an event between two
relative degrees only when the event preserves their common normal velocity.
The finite event sets and read points remain arbitrary caller-supplied data.
The strict-degree nilpotence of `PositiveDegrees.shiftedLowerStep` applies
without further geometric hypotheses. The degree bookkeeping follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h H ι)

section Event

/-- The coefficient of the difference between the truncated BCH action of the
event's label and the identity, between two retained relative degrees. -/
def eventBlock (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K)) (n m : d.cutoff k) :
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  PositiveDegrees.labelBlock d ℳ p ℒ k
    ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) n m

omit [IsWallAnnihilating H ℳ] in
/-- The event block is the generic label block at the event's truncated label. -/
theorem eventBlock_eq (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K))
    (n m : d.cutoff k) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m =
      PositiveDegrees.labelBlock d ℳ p ℒ k
        ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) n m := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- An event block outside the strict relative-degree relation vanishes. -/
theorem eventBlock_eq_zero_of_not_precedes (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) {n m : d.cutoff k} (hnm : ¬ d.Precedes m.val n.val) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m = 0 := by
  rw [eventBlock_eq]
  exact PositiveDegrees.labelBlock_eq_zero_of_not_precedes d ℳ p ℒ k _ hnm

open Classical in
/-- The lower-degree step carried by the diagram's event blocks. An event is
used only between degrees with matching normal velocities; the event sets and
read points are arbitrary inputs. -/
def eventEndpointStep (k K : ℕ) (hkK : k ≤ K)
    (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V) :
    PositiveDegrees.ShiftedEndpointFunction d ℳ p V k →ₗ[R]
      PositiveDegrees.ShiftedEndpointFunction d ℳ p V k :=
  PositiveDegrees.shiftedLowerStep d ℳ p k events
    (fun b n m _ =>
      if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
          b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
        eventBlock d ℳ p ℒ H h B k K hkK b n m
      else 0) point

omit [IsWallAnnihilating H ℳ] in
open Classical in
/-- Evaluation of the event endpoint step as a finite sum over lower-degree
coefficients with preserved normal velocity. -/
theorem eventEndpointStep_apply (k K : ℕ) (hkK : k ≤ K)
    (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V)
    (F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V k) (Q : V) (n : d.cutoff k) :
    eventEndpointStep d ℳ p ℒ H h B k K hkK events point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff k,
        if _hmn : d.Precedes m.val n.val then
          (if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
              b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
            eventBlock d ℳ p ℒ H h B k K hkK b n m
          else 0) (F (point b Q n m) m)
        else 0 := by
  apply PositiveDegrees.shiftedLowerStep_apply

omit [IsWallAnnihilating H ℳ] in
/-- The event endpoint operator is nilpotent by strict degree descent. -/
theorem eventEndpointStep_pow_eq_zero (k K : ℕ) (hkK : k ≤ K)
    (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V) :
    (eventEndpointStep d ℳ p ℒ H h B k K hkK events point) ^ (k + 1) = 0 :=
  PositiveDegrees.shiftedLowerStep_pow_eq_zero d ℳ p k events _ point

end Event

end Mei.ModuleProbe
