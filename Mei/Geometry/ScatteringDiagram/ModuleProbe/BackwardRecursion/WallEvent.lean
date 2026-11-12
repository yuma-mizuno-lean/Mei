/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Endpoint
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Recursion.Domains

/-!
# Probe and weighted-ray recurrences on the same event cuts

Choose degree-dependent generic endpoint domains and realize both the independent
probe recurrence and the weighted decorated-ray recurrence on the same complete
backward segment, simultaneous events and incoming read points. The probe formula
holds for every sufficiently small event displacement; the weighted-ray formula
selects event displacements below that bound. Strictly preceding compatible reads
are generic for their own degree domains, including zero coefficient terms.

This is a comparison of the two concrete positive-degree component equations.
The event displacements may depend on the weighted-ray coefficient and source
cell. We do not identify source components or assert a coefficient-independent
operator or equality of the two fields. We combine
`exists_wallEventRecursionDomains`, `exists_eventwiseProbeStepArrangement`, and
`exists_incomingSegmentArrangement`. The backward-ray interpretation follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (DirectedWallSpaces)

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

local notation "evaluation" k:max b:max C:max Q:max =>
  cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) b C Q

/-- The actual probe and weighted-ray fields satisfy their respective positive-degree
recurrences on exactly the same event cuts. Every preceding compatible read is
in its own generic domain. The independently constructed probe input function
agrees with the actual lower-cutoff field. No equality of the two fields or their
sources is assumed. -/
theorem exists_commonProbeWallEventRecursionDomains
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (hout : ∀ n : d.cutoff (k + 1), n.val ≠ 0 →
      ∀ b, Sum.inr b ∈ D.active (k + 2) →
        (p + n.val, 1) ∈ (D.wall (.inr b)).ray.rayDegrees →
          (D.wall (.inr b)).Outgoing)
    (A : ExceptionalArrangement V) :
    ∃ (F : d.cutoff (k + 1) → ExceptionalArrangement V)
      (f : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1)),
      (∀ n Q, (F n).IsGeneric Q → A.IsGeneric Q) ∧
      (∀ (z : WallComplement (B.activeSupport k)) (m : d.cutoff k),
        let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
          ⟨(d.mem_cutoff.mp m.property).1,
            (d.mem_cutoff.mp m.property).2.trans
              (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
        f z.val m' = (component k m) (field k (hBc.mono (Nat.le_succ k)) z)) ∧
      ∀ n : d.cutoff (k + 1), n.val ≠ 0 → ∀ Q, (F n).IsGeneric Q →
        ∃ y : WallComplement (B.activeSupport (k + 1)), y.val = Q ∧
          ∀ᶠ T : ℝ in atTop,
            0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y),
              x.val = Q + T • i (ρ (p + n.val)) ∧
              ∀ (b : (d.shiftedQuotientGrading ℳ p (k + 1)).piece 0) (C : Set V),
                ∀ θ > 0, ∃ η : WallEvent (B.active (k + 1)) → ℝ,
                  (∀ c ∈ segmentWallEvents (B.activeNormal (k + 1)) e,
                    0 < η c ∧ η c < θ ∧
                    ∀ m : d.cutoff (k + 1), d.Precedes m.val n.val →
                      c.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
                          c.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
                        (F m).IsGeneric (Q +
                          segmentEventParameter (B.activeNormal (k + 1)) e T c •
                            i (ρ (p + n.val)) + η c • i (ρ (p + m.val)))) ∧
                  let U := eventEndpointStep d ℳ p ℒ H h B
                    (k + 1) (k + 1) (Nat.le_refl _)
                    (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                    (fun c X r m => X +
                      segmentEventParameter (B.activeNormal (k + 1)) e T c •
                        i (ρ (p + r.val)) + η c • i (ρ (p + m.val)))
                  (component (k + 1) n) (field (k + 1) hBc y) = U f Q n ∧
                  (component (k + 1) n) (evaluation (k + 1) b C Q) =
                    U (fun X m => (component (k + 1) m)
                      (evaluation (k + 1) b C X)) Q n := by
  classical
  -- Reuse the independently constructed extension of the lower-cutoff field.
  obtain ⟨_, f, hf, -⟩ := exists_backwardRayEndpointStepArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial k hBc hD hB
    (fun n hn => hout n (by intro hz; rw [hz, map_zero] at hn; omega)) A
  obtain ⟨G, hG⟩ := exists_eventwiseProbeStepArrangement
    d ℳ p ℒ H h h' D B k hBc hD hB A
  obtain ⟨I, hI⟩ := exists_incomingSegmentArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB
  obtain ⟨F, hFA, hF⟩ := exists_wallEventRecursionDomains
    d ℳ p ℒ H h B k (A.union (G.union I))
  refine ⟨F, f, fun n Q hQ => (ExceptionalArrangement.isGeneric_union.mp
    (hFA n Q hQ)).1, hf, fun n hn Q hQ => ?_⟩
  obtain ⟨-, hQG, hQI⟩ := (ExceptionalArrangement.isGeneric_union.mp
    (hFA n Q hQ)).imp_right ExceptionalArrangement.isGeneric_union.mp
  obtain ⟨y, hy, hrec⟩ := hF n hn Q hQ
  obtain ⟨y', hy', hfar⟩ := hI Q hQI
  refine ⟨y, hy, ?_⟩
  filter_upwards [hrec, hfar n (hout n hn)] with T hrec hfar
  obtain ⟨hT, htail, x, e, hx, he⟩ := hrec
  obtain ⟨-, x', _, hx', hvalue⟩ := hfar
  have hxx : x' = x := WallComplement.ext (hx'.trans hx.symm)
  have hne : p ≠ p + n.val := by
    intro heq
    exact hn (by simpa only [left_eq_add] using heq)
  have hzero : (component (k + 1) n) (field (k + 1) hBc x) = 0 := by
    simpa only [hxx] using hvalue.trans
      (Subtype.ext (DirectSum.decompose_of_mem_ne ℳ a.property hne))
  have hxy : x.val - y.val = T • i (ρ (p + n.val)) := by rw [hx, hy]; module
  obtain ⟨ε, hε, hprobe⟩ := hG x y (hy ▸ hQG) e n T hT hxy f hf
  refine ⟨hT, htail, x, e, hx, fun b C θ hθ => ?_⟩
  obtain ⟨η, hη, hray⟩ := he b C (min θ ε) (lt_min hθ hε)
  have hprobe' := (hprobe η (fun c hc =>
    ⟨(hη c hc).1, ((hη c hc).2.1).trans_le (min_le_right _ _)⟩)).2
  refine ⟨η, fun c hc => ⟨(hη c hc).1,
    ((hη c hc).2.1).trans_le (min_le_left _ _), (hη c hc).2.2⟩, ?_, hray⟩
  simpa only [hy, hzero, zero_add] using hprobe'

end Mei.ModuleProbe
