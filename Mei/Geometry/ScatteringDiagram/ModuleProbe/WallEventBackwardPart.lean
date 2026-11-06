/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Algebra.Lie.Filtered.Adapted

/-!
# The backward part of simultaneous wall-event propagation

The canonical simultaneous wall-event propagation of
`Mei.ModuleProbe.WallEventEvaluation` is the truncated BCH action of the event label.
By `Mei.ModuleFiltration.truncatedBCHAction_isAdapted` it is the identity plus a
filtration-raising endomorphism, and its backward operator `1 - propagation` is
nilpotent after `k + 1` steps at coefficient order `k`.

Iterating the propagation therefore terminates: a word of simultaneous events acts as
the identity plus a raising endomorphism, and the backward recursion of a single event
has the unique solution given by the finite geometric series of its backward operator.
This is the coefficient-level form of the backward-ray recursion: each application of
the backward operator reads strictly lower relative degree, so no infinite iteration is
needed.

Nothing here assumes commutativity of the labels, a nonzero spatial direction, or a
coefficient basis. These are the statements that a last-change decomposition of a
weighted evaluation feeds into.
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

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

omit [IsWallAnnihilating H ℳ] in
/-- A single simultaneous wall event is the identity plus a filtration-raising part. -/
theorem wallEventPropagation_isAdapted (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) :
    Mei.ModuleFiltration.IsAdapted (F := A) k
      (wallEventPropagation d ℳ p ℒ H h B k K hkK b) := by
  rw [wallEventPropagation_def]
  exact Mei.ModuleFiltration.truncatedBCHAction_isAdapted A d ℒ k _

omit [IsWallAnnihilating H ℳ] in
/-- The backward operator of a simultaneous wall event is nilpotent: `k + 1` applications
exhaust the coefficient orders retained at order `k`. -/
theorem wallEventPropagation_backwardPart_pow_eq_zero (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) :
    (Mei.ModuleFiltration.backwardPart (F := A)
      (wallEventPropagation d ℳ p ℒ H h B k K hkK b)) ^ (k + 1) = 0 :=
  Mei.ModuleFiltration.IsAdapted.backwardPart_pow_eq_zero (F := A)
    (wallEventPropagation_isAdapted d ℳ p ℒ H h B k K hkK b)

omit [IsWallAnnihilating H ℳ] in
/-- A word of simultaneous wall events is the identity plus a filtration-raising part. -/
theorem isAdapted_wallEventPropagation_list_prod (k K : ℕ) (hkK : k ≤ K)
    (l : List (WallEvent (B.active K))) :
    Mei.ModuleFiltration.IsAdapted (F := A) k ((l.map fun b =>
      wallEventPropagation d ℳ p ℒ H h B k K hkK b).prod) := by
  induction l with
  | nil => simpa using (Mei.ModuleFiltration.IsAdapted.one (F := A) (k := k))
  | cons b bs ih =>
    rw [List.map_cons, List.prod_cons]
    exact Mei.ModuleFiltration.IsAdapted.mul (F := A)
      (wallEventPropagation_isAdapted d ℳ p ℒ H h B k K hkK b) ih

omit [IsWallAnnihilating H ℳ] in
/-- The backward operator of a word of simultaneous wall events is nilpotent. -/
theorem wallEventPropagation_list_prod_backwardPart_pow_eq_zero (k K : ℕ) (hkK : k ≤ K)
    (l : List (WallEvent (B.active K))) :
    (Mei.ModuleFiltration.backwardPart (F := A) ((l.map fun b =>
      wallEventPropagation d ℳ p ℒ H h B k K hkK b).prod)) ^ (k + 1) = 0 :=
  Mei.ModuleFiltration.IsAdapted.backwardPart_pow_eq_zero (F := A)
    (isAdapted_wallEventPropagation_list_prod d ℳ p ℒ H h B k K hkK l)

omit [IsWallAnnihilating H ℳ] in
/-- Every solution of the backward recursion of a simultaneous wall event is the finite sum
of the iterates of its backward operator. -/
theorem wallEventPropagation_eq_of_eq_add (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K))
    {a x : Mei.ModuleFiltration.quotient (F := A) k}
    (hx : x = a + Mei.ModuleFiltration.backwardPart (F := A)
      (wallEventPropagation d ℳ p ℒ H h B k K hkK b) x) :
    x = ∑ j ∈ Finset.range (k + 1),
      ((Mei.ModuleFiltration.backwardPart (F := A)
        (wallEventPropagation d ℳ p ℒ H h B k K hkK b)) ^ j) a :=
  Mei.ModuleFiltration.IsAdapted.eq_sum_of_eq_add (F := A)
    (wallEventPropagation_isAdapted d ℳ p ℒ H h B k K hkK b) hx

end Mei.ModuleProbe
