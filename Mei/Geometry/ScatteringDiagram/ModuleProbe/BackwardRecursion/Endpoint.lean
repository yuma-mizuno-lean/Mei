/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Straight

/-!
# The probe endpoint step along complete backward rays

The independent probe field satisfies the event endpoint step in every highest
retained positive degree, using straight incoming cuts in the input degree's
direction. The lower-coefficient endpoint function is constructed from the actual
probe field. Every cut that enters the formula avoids a prescribed exceptional
arrangement. A complete backward segment records all simultaneous encounters;
its distant initial term vanishes by outgoingness.

This combines `exists_straightProbeStepArrangement` with
`exists_incomingSegmentArrangement`. Zero spatial directions, coincident walls,
and nonzero shifts in the kernel of the spatial projection are retained. The
backward-ray interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

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
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)

/-- The positive-degree probe recurrence in the common endpoint operator, at
straight generic incoming cuts. The constructed endpoint function agrees with
all actual lower-cutoff components. Every sufficiently long backward segment
contains all encounters, and all sufficiently small common displacements give
the formula. Only additional probe walls carrying a highest retained degree
must be outgoing. This is the component equation at that cutoff. -/
theorem exists_backwardRayEndpointStepArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (hout : ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
      ∀ b, Sum.inr b ∈ D.active (k + 2) →
        (p + n.val, 1) ∈ (D.wall (.inr b)).ray.rayDegrees →
          (D.wall (.inr b)).Outgoing)
    (F : ExceptionalArrangement V) :
    ∃ (G : ExceptionalArrangement V)
      (f : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1)),
      (∀ (z : WallComplement (B.activeSupport k)) (m : d.cutoff k),
        let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
          ⟨(d.mem_cutoff.mp m.property).1,
            (d.mem_cutoff.mp m.property).2.trans
              (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
        f z.val m' = (component k m) (field k (hBc.mono (Nat.le_succ k)) z)) ∧
      ∀ Q, G.IsGeneric Q →
        ∃ y : WallComplement (B.activeSupport (k + 1)), y.val = Q ∧
          ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
            ∀ᶠ T : ℝ in atTop, 0 < T ∧
              (∀ s ≥ T, ∀ c : B.active (k + 1),
                Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
              ∃ (x : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y),
                x.val = Q + T • i (ρ (p + n.val)) ∧
                ∀ᶠ δ : ℝ in 𝓝[>] 0,
                  (∀ b ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                    ∀ m : d.cutoff (k + 1),
                      b.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                        b.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                      F.IsGeneric (Q +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + n.val)) + δ • i (ρ (p + m.val)))) ∧
                  (component (k + 1) n) (field (k + 1) hBc y) =
                    eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                      (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                      (fun b X r m => X +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + r.val)) + δ • i (ρ (p + m.val))) f Q n := by
  classical
  obtain ⟨A, hA⟩ := exists_incomingSegmentArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB
  obtain ⟨G, hG⟩ := exists_straightProbeStepArrangement
    d ℳ p ℒ H h h' D B k hBc hD hB F
  -- Totalize the genuine lower components. Higher-degree and nonallowed
  -- values can be zero because the event step never reads them.
  let f : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) := fun Q m =>
    if hm : m.val ∈ d.cutoff k then
      if hQ : ∀ c : B.active k, Q ∉ (B.wall c).support then
        (component k (⟨m.val, hm⟩ : d.cutoff k))
          (field k (hBc.mono (Nat.le_succ k)) ⟨Q, hQ⟩)
      else 0
    else 0
  have hf (z : WallComplement (B.activeSupport k)) (m : d.cutoff k) :
      let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
        ⟨(d.mem_cutoff.mp m.property).1,
          (d.mem_cutoff.mp m.property).2.trans (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
      f z.val m' = (component k m) (field k (hBc.mono (Nat.le_succ k)) z) := by
    dsimp only [f]
    rw [dite_eq_left m.property, dite_eq_left z.notMem]
  refine ⟨A.union G, f, hf, fun Q hQ => ?_⟩
  obtain ⟨hQA, hQG⟩ := ExceptionalArrangement.isGeneric_union.mp hQ
  obtain ⟨y, hy, hsegment⟩ := hA Q hQA
  refine ⟨y, hy, fun n hn => ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsegment n (hout n hn)] with T hT hseg
  obtain ⟨htail, x, e, hx, hvalue⟩ := hseg
  have hne : p ≠ p + n.val := by
    intro he
    have hn0 : n.val = 0 := by simpa only [left_eq_add] using he
    rw [hn0, map_zero] at hn
    omega
  have hzero : (component (k + 1) n) (field (k + 1) hBc x) = 0 :=
    hvalue.trans (Subtype.ext (DirectSum.decompose_of_mem_ne ℳ a.property hne))
  refine ⟨hT, htail, x, e, hx, ?_⟩
  have hxy : x.val - y.val = T • i (ρ (p + n.val)) := by rw [hx, hy]; module
  filter_upwards [hG x y (hy ▸ hQG) e n hn T hT hxy f hf] with δ hδ
  simpa only [hy, hzero, zero_add] using hδ

end Mei.ModuleProbe
