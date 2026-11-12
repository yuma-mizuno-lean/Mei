/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Recursion.Generic

/-!
# Degree-dependent generic domains for wall-event recursions

Construct one exceptional arrangement for each retained relative degree so that
all normal-compatible strictly lower event inputs are generic for their own
arrangements. The construction iterates `exists_wallEventRecursionArrangement_generic`
and takes a union at each step. Strict degree descent ensures that every required
input domain was handled at an earlier step.

The actual weighted ray evaluation satisfies the event recurrence on these
simultaneously chosen domains. Read closure is proved from the geometric
refinement, rather than assumed. The initial exceptional arrangement remains
excluded in every degree. The arrangements are chosen before endpoints, incoming
coefficients or source cells; the small displacements may depend on the segment
and coefficient, as in the underlying geometric recurrence.

This supplies compatible domains for local lower-degree recursion comparisons.
It does not identify the independent probe recurrence or prove the source
component equation. Simultaneous events, zero component maps and shifts with
zero spatial direction retain the conventions of the existing event operator.
The backward-ray method follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

open TauCeti (WallComplement)


public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex TauCeti.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)

local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)
local notation "evaluation" k:max a:max C:max Q:max =>
  cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) a C Q

open Classical in
/-- Choose all degree-dependent exceptional arrangements simultaneously, with
actual backward-ray recurrences whose strictly preceding, normal-compatible
inputs lie in their own generic domains. Every output domain also avoids the
initial arrangement. The domains require no incoming coefficient or source cell. -/
theorem exists_wallEventRecursionDomains (k : ℕ) (A : ExceptionalArrangement V) :
    ∃ E : d.cutoff (k + 1) → ExceptionalArrangement V,
      (∀ n Q, (E n).IsGeneric Q → A.IsGeneric Q) ∧
      ∀ n : d.cutoff (k + 1), n.val ≠ 0 → ∀ Q, (E n).IsGeneric Q →
        ∃ y : WallComplement (B.activeSupport (k + 1)), y.val = Q ∧
          ∀ᶠ T : ℝ in atTop,
            0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y),
              x.val = Q + T • i (ρ (p + n.val)) ∧
              ∀ (a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V),
                ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
                  (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                    0 < η b ∧ η b < θ ∧
                    ∀ m : d.cutoff (k + 1), d.Precedes m.val n.val →
                      b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                          b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                        (E m).IsGeneric (Q +
                          segmentEventParameter (B.activeNormal (k + 1)) e T b •
                            i (ρ (p + n.val)) + η b • i (ρ (p + m.val)))) ∧
                  (component (k + 1) n) (evaluation (k + 1) a C Q) =
                    eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                      (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                      (fun b X r m => X +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + r.val)) + η b • i (ρ (p + m.val)))
                      (fun X m => (component (k + 1) m) (evaluation (k + 1) a C X)) Q n := by
  classical
  choose next hnext using fun F : ExceptionalArrangement V =>
    exists_wallEventRecursionArrangement_generic d ℳ p ℒ H h B k F
  let domains : ℕ → ExceptionalArrangement V := Nat.rec A (fun _ F => F.union (next F))
  have hdomains (j l : ℕ) (hjl : j ≤ l) (Q : V)
      (hQ : (domains l).IsGeneric Q) : (domains j).IsGeneric Q := by
    induction l, hjl using Nat.le_induction with
    | base => exact hQ
    | succ l hjl ih =>
      -- Expose the successor of the local recursive arrangement sequence.
      change ((domains l).union (next (domains l))).IsGeneric Q at hQ
      exact ih (ExceptionalArrangement.isGeneric_union.mp hQ).1
  refine ⟨fun n => domains (d.degree n.val).toNat, fun n Q hQ =>
    hdomains 0 _ (Nat.zero_le _) Q hQ, fun n hn Q hQ => ?_⟩
  have hnpos := d.degree_pos (d.mem_cutoff.mp n.property).1 hn
  have hnstep : (d.degree n.val).toNat = ((d.degree n.val).toNat - 1) + 1 := by omega
  dsimp only at hQ
  rw [hnstep] at hQ
  -- The positive output degree selects a successor of the arrangement sequence.
  change ((domains ((d.degree n.val).toNat - 1)).union
    (next (domains ((d.degree n.val).toNat - 1)))).IsGeneric Q at hQ
  obtain ⟨y, hy, hrec⟩ := hnext (domains ((d.degree n.val).toNat - 1)) Q
    (ExceptionalArrangement.isGeneric_union.mp hQ).2
  refine ⟨y, hy, ?_⟩
  filter_upwards [hrec n hn] with T hT
  obtain ⟨hT, htail, x, e, hx, he⟩ := hT
  refine ⟨hT, htail, x, e, hx, fun a C θ hθ => ?_⟩
  obtain ⟨η, hη, heq⟩ := he a C θ hθ
  refine ⟨η, fun b hb => ⟨(hη b hb).1, (hη b hb).2.1, fun m hmn hnormal => ?_⟩, heq⟩
  apply hdomains _ ((d.degree n.val).toNat - 1) _ _ ((hη b hb).2.2 m hnormal)
  have hmnonneg := d.degree_nonneg (d.mem_cutoff.mp m.property).1
  have hlt := d.degree_lt_of_precedes hmn
  omega

end Mei.ModuleProbe
