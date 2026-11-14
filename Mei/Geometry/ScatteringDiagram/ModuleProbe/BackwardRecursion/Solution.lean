/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Domains
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block.Degree

/-!
# A finite recursive solution for the actual coherent probe field

At one ambient coefficient cutoff, choose actual complete backward segments at
each positive output degree and assemble their event rows into one lower-degree
operator. The compatible generic domains are constructed geometrically. The
leading component is the incoming coefficient, and strict-degree nilpotence
then identifies the actual probe field with the finite recursive sum locally.

The geometric event inventory varies with the output degree. No identification
with a fixed-inventory decorated-ray operator, or equality of probe and ray
evaluations, is asserted. Zero spatial directions and positive shifts in the
kernel of the spatial projection retain the conventions of the backward-ray
construction. The method follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

open TauCeti (WallComplement)

public noncomputable section

open TauCeti (ExceptionalArrangement)

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex TauCeti.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
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

variable (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')



/-- The actual common-cutoff probe field is a finite recursive sum on compatible
generic domains. The selected event inventories and positive incoming cuts come
from complete backward segments at each output's own geometric cutoff. -/
theorem exists_coherentProbeEndpoint_finiteRecursion
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (K : ℕ) (hBc : B.LevelConsistent K) (hD : D.LevelConsistent (K + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) K)
    (hout : ∀ n : d.cutoff K, ∀ b, Sum.inr b ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr b)).ray.rayDegrees →
        (D.wall (.inr b)).Outgoing)
    (A : ExceptionalArrangement ℝ V) :
    ∃ (E : d.cutoff K → ExceptionalArrangement ℝ V)
      (events : (Q : V) → (n : d.cutoff K) →
        Finset (WallEvent (B.active (d.degree n.val).toNat)))
      (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
        V → d.cutoff K → V),
      let U := degreeEventEndpointStep d ℳ p ℒ H h B K events point
      let F := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B K K (Nat.le_refl _) hBc
      let source : PositiveDegrees.ShiftedEndpointFunction d ℳ p V K :=
        fun _ n => DirectSum.decompose ℳ (a : M) (p + n.val)
      (∀ n Q, (E n).IsGeneric Q → A.IsGeneric Q ∧
        ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      (∀ Q n, (¬ (E n).IsGeneric Q ∨ n.val = 0) → events Q n = ∅) ∧
      (∀ Q n, (E n).IsGeneric Q → n.val ≠ 0 →
        ∃ (T δ : ℝ) (x y : WallComplement (B.activeSupport (d.degree n.val).toNat))
          (e : x ⟶ y),
          0 < T ∧ 0 < δ ∧ y.val = Q ∧ x.val = Q + T • i (ρ (p + n.val)) ∧
          (∀ s ≥ T, ∀ c : B.active (d.degree n.val).toNat,
            Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
          events Q n = segmentWallEvents (B.activeNormal (d.degree n.val).toNat) e ∧
          ∀ b ∈ events Q n, ∀ m, point n b Q m = Q +
            segmentEventParameter (B.activeNormal (d.degree n.val).toNat) e T b •
              i (ρ (p + n.val)) + δ • i (ρ (p + m.val))) ∧
      (∀ Q n, (E n).IsGeneric Q → ∀ b ∈ events Q n, ∀ m,
        d.Precedes m.val n.val →
        b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
          b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val))) →
        (E m).IsGeneric (point n b Q m)) ∧
      U ^ (K + 1) = 0 ∧
      (∀ Q n, (E n).IsGeneric Q → F Q n = source Q n + U F Q n) ∧
      ∀ n, EqOn (F · n) ((Module.End.finiteRecursion U (K + 1) source) · n)
        {Q | (E n).IsGeneric Q} := by
  classical
  obtain ⟨E, hEA, hE⟩ := exists_coherentProbeRecursionDomains
    d ℳ p ℒ H h h' D₀ a D B hinitial K hBc hD hB hout A
  let F := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B K K (Nat.le_refl _) hBc
  have hselect (Q : V) (n : d.cutoff K) (hQ : (E n).IsGeneric Q)
      (hn : n.val ≠ 0) := hE n hn Q hQ
  choose hnK y hy hsegments using hselect
  choose T hT using fun Q n hQ hn => (hsegments Q n hQ hn).exists
  choose hTpos htail x e hx hcuts using hT
  have hchoose (Q : V) (n : d.cutoff K) (hQ : (E n).IsGeneric Q) (hn : n.val ≠ 0) :=
    ((hcuts Q n hQ hn).and self_mem_nhdsWithin).exists
  choose δ hδ using hchoose
  let events (Q : V) (n : d.cutoff K) :=
    if hQ : (E n).IsGeneric Q then
      if hn : n.val ≠ 0 then
        segmentWallEvents (B.activeNormal (d.degree n.val).toNat) (e Q n hQ hn)
      else ∅
    else ∅
  let point (n : d.cutoff K) (b : WallEvent (B.active (d.degree n.val).toNat))
      (Q : V) (m : d.cutoff K) :=
    if hQ : (E n).IsGeneric Q then
      if hn : n.val ≠ 0 then
        Q + segmentEventParameter (B.activeNormal (d.degree n.val).toNat)
          (e Q n hQ hn) (T Q n hQ hn) b • i (ρ (p + n.val)) +
            δ Q n hQ hn • i (ρ (p + m.val))
      else Q
    else Q
  let U := degreeEventEndpointStep d ℳ p ℒ H h B K events point
  let source : PositiveDegrees.ShiftedEndpointFunction d ℳ p V K :=
    fun _ n => DirectSum.decompose ℳ (a : M) (p + n.val)
  have hrestrict (j : ℕ) (hjK : j ≤ K) :
      PositiveDegrees.shiftedEndpointRestrict d ℳ p hjK F =
        coherentProbeEndpointFunction d ℳ p ℒ H h h' D B j K hjK hBc := by
    funext Q m
    rw [PositiveDegrees.shiftedEndpointRestrict_apply]
    exact coherentProbeEndpointFunction_cutoff_inclusion d ℳ p ℒ H h h' D B
      hjK (Nat.le_refl K) hBc Q m
  have hread (Q : V) (n : d.cutoff K) (hQ : (E n).IsGeneric Q)
      (b : WallEvent (B.active (d.degree n.val).toNat)) (hb : b ∈ events Q n)
      (m : d.cutoff K) (hmn : d.Precedes m.val n.val)
      (hnormal : b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
        b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val)))) :
      (E m).IsGeneric (point n b Q m) := by
    have hn : n.val ≠ 0 := by
      intro hn
      simp only [events, hQ, ↓reduceDIte, hn, ne_eq, not_true_eq_false,
        Finset.notMem_empty] at hb
    simp only [events, dite_eq_left hQ, dite_eq_left hn] at hb
    simpa only [point, dite_eq_left hQ, dite_eq_left hn,
      PositiveDegrees.precedingDegreeCutoffIndex_val] using
      (hδ Q n hQ hn).1.1 b hb (d.precedingDegreeCutoffIndex n m hmn) hmn hnormal
  have hrec (Q : V) (n : d.cutoff K) (hQ : (E n).IsGeneric Q) :
      F Q n = source Q n + U F Q n := by
    by_cases hn : n.val = 0
    · have hcomponent : F Q n = source Q n := by
        dsimp only [F]
        rw [coherentProbeEndpointFunction_apply_of_allowed d ℳ p ℒ H h h' D B
          K K (Nat.le_refl _) hBc Q n (hEA n Q hQ).2]
        dsimp only [source]
        generalize_proofs hcut
        generalize hq : p + n.val = q at hcut ⊢
        rw [hn, add_zero] at hq
        subst q
        have hdecomp : DirectSum.decompose ℳ (a : M) p = a :=
          Subtype.ext (DirectSum.decompose_of_mem_same ℳ a.property)
        rw [hdecomp]
        exact shiftedQuotientComponent_extendedCoefficientField_self d ℳ p ℒ H h h'
          D₀ a D B hinitial K hD hBc hB
          (fun b hb hray => by
            simpa only [add_zero] using hout ⟨0, by simp⟩ b
              (D.active_mono (by omega) hb) (by simpa only [add_zero] using hray))
          ⟨Q, (hEA n Q hQ).2⟩
      have hempty : events Q n = ∅ := by simp [events, hQ, hn]
      rw [hcomponent]
      dsimp only [U]
      rw [degreeEventEndpointStep_apply, hempty, Finset.sum_empty, add_zero]
    · have hsource : source Q n = 0 := by
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_ne ℳ a.property
          (by simpa only [ne_eq, left_eq_add] using hn)
      rw [hsource, zero_add]
      dsimp only [U]
      rw [degreeEventEndpointStep_apply_eq d ℳ p ℒ H h B K events point F Q n
        (hnK Q n hQ hn), hrestrict]
      have houtput := coherentProbeEndpointFunction_cutoff_inclusion d ℳ p ℒ H h h'
        D B (hnK Q n hQ hn) (Nat.le_refl K) hBc Q (d.degreeCutoffIndex n)
      have hreinclude : (⟨(d.degreeCutoffIndex n).val,
          d.cutoff_mono (hnK Q n hQ hn) (d.degreeCutoffIndex n).property⟩ : d.cutoff K) = n :=
        Subtype.ext (d.degreeCutoffIndex_val n)
      -- Compare in M so the explicit index equality acts on a constant codomain.
      have hindexVal := congrArg (fun m : d.cutoff K =>
        (coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
          K K (Nat.le_refl _) hBc Q m : M)) hreinclude
      have houtputVal := hindexVal.symm.trans (congrArg Subtype.val houtput)
      -- The index transport is explicit above; this show only unfolds the local name F.
      rw [show F Q n = coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
        (d.degree n.val).toNat K (hnK Q n hQ hn) hBc Q (d.degreeCutoffIndex n) from
          Subtype.ext houtputVal]
      simpa only [eventEndpointStep_apply, events, point, dite_eq_left hQ, dite_eq_left hn,
        PositiveDegrees.degreeCutoffIndex_val] using (hδ Q n hQ hn).1.2
  refine ⟨E, events, point, hEA, ?_, ?_, hread,
    degreeEventEndpointStep_pow_eq_zero d ℳ p ℒ H h B K events point, hrec, ?_⟩
  · intro Q n hn
    rcases hn with hQ | hn
    · simp only [events, hQ, ↓reduceDIte]
    · simp only [events, hn, ne_eq, not_true_eq_false, ↓reduceDIte, dite_eq_ite, ite_self]
  · intro Q n hQ hn
    refine ⟨T Q n hQ hn, δ Q n hQ hn, x Q n hQ hn, y Q n hQ hn, e Q n hQ hn,
      hTpos Q n hQ hn, (hδ Q n hQ hn).2, hy Q n hQ hn, hx Q n hQ hn,
      htail Q n hQ hn, ?_, ?_⟩
    · simp only [events, dite_eq_left hQ, dite_eq_left hn]
    · intro b hb m
      simp only [point, dite_eq_left hQ, dite_eq_left hn]
  · exact eqOn_degreeEventEndpointStep_finiteRecursion d ℳ p ℒ H h B K events point
      (fun n => {Q | (E n).IsGeneric Q})
      (fun Q n hQ b hb m hmn hnormal _ => hread Q n hQ b hb m hmn hnormal) source F hrec

end Mei.ModuleProbe
