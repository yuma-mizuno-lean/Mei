/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Recursion.Domains
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Source
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block.Local

/-!
# The finite backward-ray solution for actual weighted evaluations

The weighted evaluation of actual simultaneous-event rays satisfies one equation
`Θ = source + U Θ` on degree-dependent generic endpoint domains. Here `U` is the
existing nilpotent event operator, with events and read points selected from
complete admissible backward segments. Its source is the whole incoming
homogeneous coefficient. Consequently the evaluation equals the finite operator
sum on those domains, including its relative-degree-zero component.

The endpoint arrangements are independent of the incoming coefficient. The
operator's small incoming displacements are chosen for that coefficient. Every
normal-compatible preceding read lies in its own generic domain, including reads
whose blocks vanish. Outside the domains, and in relative degree zero, the event
sets are empty. The finite-sum comparison requires no recurrence at exceptional
endpoints. Simultaneous indexed encounters and shifts with zero spatial direction
are retained by the existing actual-ray recurrence.

We combine `exists_wallEventRecursionDomains`, the leading-component theorem,
and local nilpotent-recursion uniqueness. The backward-ray interpretation follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

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

local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)
local notation "evaluation" k:max a:max Q:max =>
  cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) a univ Q

/-- Actual weighted ray evaluations are finite nilpotent-recursion solutions on
generic endpoint domains. The event inventory and read points come from complete
backward segments, and every compatible lower-degree read is generic for its own
domain. The domains are chosen before the incoming coefficient; the event cuts
may depend on it. The source is the incoming homogeneous coefficient, with zero
components in every positive relative degree. -/
theorem exists_cutoffWallEventEvaluation_finiteRecursion (k : ℕ)
    (A : ExceptionalArrangement V) :
    ∃ E : d.cutoff (k + 1) → ExceptionalArrangement V,
      (∀ n Q, (E n).IsGeneric Q → A.IsGeneric Q) ∧
      ∀ a : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0,
        ∃ (events : V → d.cutoff (k + 1) → Finset (WallEvent (B.active (k + 1))))
          (point : WallEvent (B.active (k + 1)) → V →
            (n m : d.cutoff (k + 1)) → V),
          let U := eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1)
            (Nat.le_refl _) events point
          let source : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) :=
            fun _ n => (component (k + 1) n) a
          let Θ : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) :=
            fun Q n => (component (k + 1) n) (evaluation (k + 1) a Q)
          (∀ Q n, (¬ (E n).IsGeneric Q ∨ n.val = 0) → events Q n = ∅) ∧
          (∀ Q n, (E n).IsGeneric Q → n.val ≠ 0 →
            ∃ (T : ℝ) (x y : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y)
              (η : WallEvent (B.active (k + 1)) → ℝ),
              0 < T ∧ y.val = Q ∧ x.val = Q + T • i (ρ (p + n.val)) ∧
              (∀ s ≥ T, ∀ c : B.active (k + 1),
                Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
              events Q n = segmentWallEvents (B.activeNormal (k + 1)) e ∧
              ∀ b ∈ events Q n, 0 < η b ∧ η b < 1 ∧
                ∀ m, point b Q n m = Q +
                  segmentEventParameter (B.activeNormal (k + 1)) e T b •
                    i (ρ (p + n.val)) + η b • i (ρ (p + m.val))) ∧
          (∀ Q n, (E n).IsGeneric Q → ∀ b ∈ events Q n, ∀ m,
            d.Precedes m.val n.val →
            b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
              b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
            (E m).IsGeneric (point b Q n m)) ∧
          (∀ Q n, (E n).IsGeneric Q → Θ Q n = source Q n + U Θ Q n) ∧
          ∀ n, EqOn (Θ · n) ((Module.End.finiteRecursion U (k + 2) source) · n)
            {Q | (E n).IsGeneric Q} := by
  classical
  obtain ⟨S, hS⟩ := exists_cutoffWallEventEvaluation_leadingComponentArrangement
    d ℳ p ℒ H h B (k + 1)
  obtain ⟨E, hEA, hE⟩ := exists_wallEventRecursionDomains
    d ℳ p ℒ H h B k (A.union S)
  refine ⟨E, fun n Q hQ => (ExceptionalArrangement.isGeneric_union.mp (hEA n Q hQ)).1,
    fun a => ?_⟩
  let Θ : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) :=
    fun Q n => (component (k + 1) n) (evaluation (k + 1) a Q)
  -- Choose an actual complete segment and its small event displacements for
  -- each generic endpoint and positive output degree.
  have hselect (Q : V) (n : d.cutoff (k + 1)) (hQ : (E n).IsGeneric Q)
      (hn : n.val ≠ 0) := hE n hn Q hQ
  choose y hy hsegments using hselect
  choose T hT using fun Q n hQ hn => (hsegments Q n hQ hn).exists
  choose hTpos htail x e hx hcuts using hT
  choose η hη heq using fun Q n hQ hn => hcuts Q n hQ hn a univ 1 zero_lt_one
  let events (Q : V) (n : d.cutoff (k + 1)) :=
    if hQ : (E n).IsGeneric Q then
      if hn : n.val ≠ 0 then
        segmentWallEvents (B.activeNormal (k + 1)) (e Q n hQ hn)
      else ∅
    else ∅
  let point (b : WallEvent (B.active (k + 1))) (Q : V) (n m : d.cutoff (k + 1)) :=
    if hQ : (E n).IsGeneric Q then
      if hn : n.val ≠ 0 then
        Q + segmentEventParameter (B.activeNormal (k + 1))
          (e Q n hQ hn) (T Q n hQ hn) b • i (ρ (p + n.val)) +
            η Q n hQ hn b • i (ρ (p + m.val))
      else Q
    else Q
  let U := eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1)
    (Nat.le_refl _) events point
  let source : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) :=
    fun _ n => (component (k + 1) n) a
  have hread (Q : V) (n : d.cutoff (k + 1)) (hQ : (E n).IsGeneric Q)
      (b : WallEvent (B.active (k + 1))) (hb : b ∈ events Q n)
      (m : d.cutoff (k + 1)) (hmn : d.Precedes m.val n.val)
      (hnormal : b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
        b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val)))) :
      (E m).IsGeneric (point b Q n m) := by
    have hn : n.val ≠ 0 := by
      intro hn
      simp only [events, hQ, ↓reduceDIte, hn, ne_eq, not_true_eq_false,
        Finset.notMem_empty] at hb
    simp only [events, dite_eq_left hQ, dite_eq_left hn] at hb
    simpa only [point, dite_eq_left hQ, dite_eq_left hn] using
      (hη Q n hQ hn b hb).2.2 m hmn hnormal
  have hrec (Q : V) (n : d.cutoff (k + 1)) (hQ : (E n).IsGeneric Q) :
      Θ Q n = source Q n + U Θ Q n := by
    by_cases hn : n.val = 0
    · have hQS := (ExceptionalArrangement.isGeneric_union.mp (hEA n Q hQ)).2
      have hleading := hS Q hQS (k + 1) (Nat.le_refl _) a
      have hcomponent : Θ Q n = source Q n := by
        dsimp only [Θ, source]
        -- Generalize the ambient index together with its dependent cutoff proof.
        generalize_proofs hcut
        generalize hq : p + n.val = q at hcut ⊢
        rw [hn, add_zero] at hq
        subst q
        exact hleading
      have hempty : events Q n = ∅ := by simp [events, hQ, hn]
      rw [hcomponent]
      dsimp only [U]
      rw [eventEndpointStep_apply, hempty, Finset.sum_empty, add_zero]
    · have hsource : source Q n = 0 :=
        d.shiftedQuotientComponent_eq_zero_of_mem ℳ p a.property
          (by simpa only [add_zero, ne_eq, left_eq_add] using hn)
          (PositiveDegrees.degree_add_val_sub_self_le d p (k + 1) n)
      rw [hsource, zero_add]
      simpa only [Θ, U, eventEndpointStep_apply, events, point, dite_eq_left hQ, dite_eq_left hn]
        using heq Q n hQ hn
  refine ⟨events, point, ?_, ?_, hread, hrec, ?_⟩
  · intro Q n hn
    rcases hn with hQ | hn
    · simp only [events, hQ, ↓reduceDIte]
    · simp only [events, hn, ne_eq, not_true_eq_false, ↓reduceDIte, dite_eq_ite,
        ite_self]
  · intro Q n hQ hn
    refine ⟨T Q n hQ hn, x Q n hQ hn, y Q n hQ hn, e Q n hQ hn, η Q n hQ hn,
      hTpos Q n hQ hn, hy Q n hQ hn, hx Q n hQ hn, htail Q n hQ hn, ?_, ?_⟩
    · simp only [events, dite_eq_left hQ, dite_eq_left hn]
    · intro b hb
      simp only [events, dite_eq_left hQ, dite_eq_left hn] at hb
      exact ⟨(hη Q n hQ hn b hb).1, (hη Q n hQ hn b hb).2.1,
        fun m => by simp only [point, dite_eq_left hQ, dite_eq_left hn]⟩
  · exact eqOn_eventEndpointStep_finiteRecursion d ℳ p ℒ H h B (k + 1) (k + 1)
      (Nat.le_refl _) events point (fun n => {Q | (E n).IsGeneric Q})
      (fun Q n hQ b hb m hmn hnormal _ => hread Q n hQ b hb m hmn hnormal)
      source Θ hrec

end Mei.ModuleProbe
