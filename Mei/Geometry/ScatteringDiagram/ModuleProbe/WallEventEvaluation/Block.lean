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
Its event blocks vanish between degrees of different normal velocity. At every
retained output degree the step reads only the preceding cutoff. The finite
event sets and read points remain arbitrary caller-supplied data.
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
theorem eventBlock_def (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K))
    (n m : d.cutoff k) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m =
      PositiveDegrees.labelBlock d ℳ p ℒ k
        ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b)) n m := (rfl)

omit [IsWallAnnihilating H ℳ] in
/-- An event block outside the strict relative-degree relation vanishes. -/
theorem eventBlock_eq_zero_of_not_precedes (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) {n m : d.cutoff k} (hnm : ¬ d.Precedes m.val n.val) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m = 0 := by
  rw [eventBlock_def]
  exact PositiveDegrees.labelBlock_eq_zero_of_not_precedes d ℳ p ℒ k _ hnm

omit [IsWallAnnihilating H ℳ] in
/-- Between distinct relative degrees, the event block is the component of the
truncated signed event action itself: the subtracted identity has no such component. -/
theorem eventBlock_apply_of_ne (k K : ℕ) (hkK : k ≤ K) (b : WallEvent (B.active K))
    (n m : d.cutoff k) (hmn : m.val ≠ n.val) (x : ℳ (p + m.val)) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m x =
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (PositiveDegrees.degree_add_val_sub_self_le d p k n)
        ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          ((d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K b))
          (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
            ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x))) := by
  rw [eventBlock_def]
  exact PositiveDegrees.labelBlock_apply_of_ne d ℳ p ℒ k _ n m hmn x

omit [IsWallAnnihilating H ℳ] in
/-- An event block vanishes between degrees of different normal velocity.
The event inventory may be retained at any higher geometric cutoff. -/
theorem eventBlock_eq_zero_of_normal_ne (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K))
    (n m : d.cutoff k)
    (hne : b.normal (B.activeNormal K) (i (ρ (p + n.val))) ≠
      b.normal (B.activeNormal K) (i (ρ (p + m.val)))) :
    eventBlock d ℳ p ℒ H h B k K hkK b n m = 0 := by
  classical
  by_cases hmn : m.val = n.val
  · exact eventBlock_eq_zero_of_not_precedes d ℳ p ℒ H h B k K hkK b
      (by simp only [d.precedes_iff, hmn, ne_eq, not_true_eq_false, false_and, not_false_eq_true])
  apply LinearMap.ext
  intro a
  rw [eventBlock_apply_of_ne d ℳ p ℒ H h B k K hkK b n m hmn]
  by_contra hnonzero
  let F := d.shiftedLieFiltration ℒ ℳ p
  let x : F.quotient K := Submodule.Quotient.mk
    (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ a)
  have hx : x ∈ (d.shiftedQuotientGrading ℳ p K).piece m.val :=
    (d.mem_shiftedQuotientGrading_iff ℳ p).mpr
      ⟨_, (mem_shiftedGrading ℳ d.monoid p).mpr
        (by simpa only [coe_shiftedInclusion] using a.property), rfl⟩
  have hdec : DirectSum.decompose (d.shiftedQuotientGrading ℳ p K).piece
      (F.truncatedBCHAction d ℒ K (B.wallEventLabel K b) x) n.val ≠ 0 := by
    intro hz
    apply hnonzero
    have hn := PositiveDegrees.degree_add_val_sub_self_le d p k n
    -- A retained component agrees with its value before truncation.
    have htransition := F.transition_truncatedBCHAction d ℒ hkK (B.wallEventLabel K b) x
    simp only [x, ModuleFiltration.transition_mk] at htransition
    rw [← htransition,
      d.shiftedQuotientComponent_transition ℳ p (p + n.val) hkK hn,
      ← d.shiftedQuotientComponent_decompose_same ℳ p K
        ⟨n.val, (d.mem_cutoff.mp n.property).1⟩
        ((d.mem_cutoff.mp n.property).2.trans (Int.ofNat_le.mpr hkK)), hz]
    exact map_zero _
  have := d.shiftedGrading_gradedBracket ℒ ℳ p
  have he := B.normal_eq_of_decompose_truncatedBCHAction_wallEventLabel_ne_zero
    (M := d.shiftedLieSubmodule ℒ ℳ p) (shiftedGrading ℳ d.monoid p) F K
    (d.shiftedQuotientGrading ℳ p K).piece (d.shiftedQuotientGrading_piece ℳ p K) b hx hdec
  apply hne
  simp only [WallEvent.normal_def, B.activeNormal_apply,
    h.continuousRealCharacter_apply, h.realCharacter_apply, map_add, he]

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
/-- The event step is the generic lower-degree step with the normal-velocity
condition applied to its coefficient blocks. -/
theorem eventEndpointStep_def (k K : ℕ) (hkK : k ≤ K)
    (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V) :
    eventEndpointStep d ℳ p ℒ H h B k K hkK events point =
      PositiveDegrees.shiftedLowerStep d ℳ p k events
        (fun b n m _ =>
          if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
              b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
            eventBlock d ℳ p ℒ H h B k K hkK b n m
          else 0) point := (rfl)

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
open Classical in
/-- At every retained output degree the endpoint step reads only the preceding
cutoff, with the event inventory fixed at any higher geometric cutoff.
The strict-degree filter is automatic in the event blocks. -/
theorem eventEndpointStep_apply_sum_cutoff (k K : ℕ) (hkK : k + 1 ≤ K)
    (events : V → (d.cutoff (k + 1)) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff (k + 1)) → V)
    (F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1))
    (Q : V) (n : d.cutoff (k + 1)) :
    eventEndpointStep d ℳ p ℒ H h B (k + 1) K hkK events point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff k,
        let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
          ⟨(d.mem_cutoff.mp m.property).1,
            (d.mem_cutoff.mp m.property).2.trans (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
        (if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
            b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
          eventBlock d ℳ p ℒ H h B (k + 1) K hkK b n m'
        else 0) (F (point b Q n m') m') := by
  rw [eventEndpointStep_apply]
  apply Finset.sum_congr rfl
  intro b hb
  let term (m : d.cutoff (k + 1)) :=
    (if b.normal (B.activeNormal K) (i (ρ (p + n.val))) =
        b.normal (B.activeNormal K) (i (ρ (p + m.val))) then
      eventBlock d ℳ p ℒ H h B (k + 1) K hkK b n m
    else 0) (F (point b Q n m) m)
  have hz (m : d.cutoff (k + 1)) (hm : ¬ d.Precedes m.val n.val) : term m = 0 := by
    dsimp only [term]
    rw [eventBlock_eq_zero_of_not_precedes d ℳ p ℒ H h B _ _ _ b hm]
    split_ifs <;> rfl
  trans ∑ m : d.cutoff (k + 1), term m
  · apply Finset.sum_congr rfl
    intro m hm
    by_cases hp : d.Precedes m.val n.val
    · simp only [hp, ↓reduceDIte, term]
    · simp only [hp, ↓reduceDIte, hz m hp]
  have hbound (m : d.cutoff (k + 1)) (hm : term m ≠ 0) : d.degree m.val ≤ k := by
    have hp : d.Precedes m.val n.val := by_contra fun hp => hm (hz m hp)
    have hd := d.degree_lt_of_precedes hp
    have hn := (d.mem_cutoff.mp n.property).2
    omega
  refine Finset.sum_bij_ne_zero (fun m _ hm =>
    (⟨m.val, d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp m.property).1, hbound m hm⟩⟩ :
      d.cutoff k)) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)
  · intro m _ hm m' _ hm' he
    exact Subtype.ext (congrArg (fun m : d.cutoff k => m.val) he)
  · intro m _ hm
    let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
      ⟨(d.mem_cutoff.mp m.property).1,
        (d.mem_cutoff.mp m.property).2.trans (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
    exact ⟨m', Finset.mem_univ _, hm, Subtype.ext rfl⟩

omit [IsWallAnnihilating H ℳ] in
/-- The event endpoint operator is nilpotent by strict degree descent. -/
theorem eventEndpointStep_pow_eq_zero (k K : ℕ) (hkK : k ≤ K)
    (events : V → (d.cutoff k) → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff k) → V) :
    (eventEndpointStep d ℳ p ℒ H h B k K hkK events point) ^ (k + 1) = 0 :=
  PositiveDegrees.shiftedLowerStep_pow_eq_zero d ℳ p k events _ point

end Event

end Mei.ModuleProbe
