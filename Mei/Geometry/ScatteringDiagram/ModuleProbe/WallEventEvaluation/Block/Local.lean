/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Local

/-!
# Comparing event recursions on generic endpoint domains

Two independent event recursions need only hold on their common endpoint
domains. Degree-dependent domains are allowed, provided every nonzero block
with matching normal velocity reads inside the lower-degree domain. Zero
blocks and mismatched velocities need no genericity hypothesis. The conclusion
compares whole coefficients and makes no assertion at exceptional endpoints.

This supplies the uniqueness step after geometric generic-input constructions;
it does not supply those constructions or assert a common probe/ray recurrence.
The proof uses the shared local lower-degree recursion theorem. Its application
to backward rays follows Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (DirectedWallSpaces)

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)
  (k K : ℕ) (hkK : k ≤ K)
  (events : V → d.cutoff k → Finset (WallEvent (B.active K)))
  (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V)
  (Ω : d.cutoff k → Set V)
  (hΩ : ∀ Q n, Q ∈ Ω n → ∀ b ∈ events Q n, ∀ m, d.Precedes m.val n.val →
    b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
      b.normal (B.activeNormal K) (i (ρ (p + m.val))) →
    eventBlock d ℳ p ℒ H h B k K hkK b n m ≠ 0 → point b Q n m ∈ Ω m)

local notation "U" => (eventEndpointStep d ℳ p ℒ H h B k K hkK events point)

include hΩ in
/-- Independent event recursions with the same incoming coefficients on their
common domains agree there. Only genuinely contributing blocks must read inside
the lower-degree domain; no equality outside the domains is assumed. -/
theorem eqOn_of_eventEndpointStep_eq_add
    (a c F G : PositiveDegrees.ShiftedEndpointFunction d ℳ p V k)
    (hac : ∀ n, Set.EqOn (a · n) (c · n) (Ω n))
    (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n + U F Q n)
    (hG : ∀ Q n, Q ∈ Ω n → G Q n = c Q n + U G Q n) :
    ∀ n, Set.EqOn (F · n) (G · n) (Ω n) := by
  classical
  simp only [eventEndpointStep_def] at hF hG
  apply PositiveDegrees.eqOn_of_shiftedLowerStep_eq_add d ℳ p k events _ point Ω
    ?_ a c F G hac hF hG
  intro Q n hQ b hb m hmn hblock
  split_ifs at hblock with hnormal
  · exact hΩ Q n hQ b hb m hmn hnormal hblock
  · exact (hblock rfl).elim

include hΩ in
/-- The unique local event-recursion values are obtained by the original finite
operator sum, for any extension of the incoming coefficients to exceptional
endpoints. All actual zero terms and simultaneous-event blocks are retained. -/
theorem eqOn_eventEndpointStep_finiteRecursion
    (a F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V k)
    (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n + U F Q n) :
    ∀ n, Set.EqOn (F · n) ((Module.End.finiteRecursion U (k + 1) a) · n) (Ω n) := by
  apply eqOn_of_eventEndpointStep_eq_add d ℳ p ℒ H h B k K hkK events point Ω hΩ
    a a F (Module.End.finiteRecursion U (k + 1) a) (fun _ _ _ => rfl) hF
  intro Q n _
  exact congrFun (congrFun (Module.End.finiteRecursion_eq_add U
    (eventEndpointStep_pow_eq_zero d ℳ p ℒ H h B k K hkK events point) a) Q) n

end Mei.ModuleProbe
