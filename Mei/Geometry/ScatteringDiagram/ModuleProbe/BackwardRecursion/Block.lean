/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block

/-!
# The probe backward-ray recurrence in canonical event blocks

The independently constructed probe field satisfies the backward recurrence in
`eventBlock`, the coefficient maps used by `eventEndpointStep`. A single
exceptional arrangement supplies complete backward segments for all highest
retained relative degrees. At every simultaneous encounter the inputs are the
actual lower-order probe components at generic incoming points. One arbitrarily
small direction perturbation works for every endpoint and every such degree.

This is the probe side of the comparison with weighted decorated rays. The
far-ray initial condition and generic-germ theorem come from
`exists_backwardRayRecursionArrangement`; no broken-line evaluation enters the
proof. The equation retains whole homogeneous coefficients and zero terms,
including degree changes invisible under the spatial projection. It does not
yet assemble the recurrences into a single equation on endpoint functions.

The backward-ray method follows Mandel, *Scattering diagrams, theta functions,
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
local notation "labels" k:max e:max => (List.map
  (crossingEventProduct (G := d.truncatedGroup ℒ k)
    (fun c : B.active k => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute k) e)
      (List.reverse (orderedCrossingTimes e)))

/-- The independent probe recurrence uses the same canonical event blocks as
the lower-degree endpoint operator. Every sufficiently long segment includes
all backward-ray encounters. At sufficiently small common displacements, its
inputs are generic for the prescribed arrangement and read the preceding
cutoff. No nonzero spatial direction or coefficient-basis hypothesis is needed.
The event times are listed in multiplication order, first crossing rightmost. -/
theorem exists_backwardRayEventBlockArrangement
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
    (F : ExceptionalArrangement V) {s : ℝ} (hs : 0 < s) :
    ∃ (E : ExceptionalArrangement V) (r : V), ‖r‖ < s ∧
      (∀ (n : d.cutoff (k + 1)) (c : B.active (k + 1)),
        h.realCharacter (B.wall c).normal (i (ρ (p + n.val))) ≠ 0 →
          0 < h.realCharacter (B.wall c).normal (i (ρ (p + n.val)) + r) *
            h.realCharacter (B.wall c).normal (i (ρ (p + n.val)))) ∧
      ∀ Q, E.IsGeneric Q →
      ∃ y : WallComplement (B.activeSupport (k + 1)),
        y.val = Q ∧ ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
          ∀ᶠ T : ℝ in atTop, 0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (B.activeSupport (k + 1))) (e : x ⟶ y),
              x.val = Q + T • i (ρ (p + n.val)) ∧
              let τ := (orderedCrossingTimes e).reverse
              let g := labels (k + 1) e
              ∀ᶠ δ : ℝ in 𝓝[>] 0,
                ∃ z : Fin g.length →
                    WallComplement (B.activeSupport k),
                  (∀ b : Fin g.length,
                    (z b).val = Q + ((1 - τ[b.val]'(by
                      simpa only [g, List.length_map] using b.isLt)) * T) •
                        i (ρ (p + n.val)) + δ • (i (ρ (p + n.val)) + r) ∧
                      F.IsGeneric (z b).val) ∧
                  d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
                    (PositiveDegrees.degree_add_val_sub_self_le d p (k + 1) n)
                    (field (k + 1) hBc y) =
                    ∑ b : Fin g.length, ∑ m : d.cutoff k,
                      eventBlock d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                        (crossingWallEvent (B.activeNormal (k + 1)) e
                          (τ[b.val]'(by
                            simpa only [g, List.length_map] using b.isLt))
                          (List.mem_reverse.mp (List.getElem_mem (by
                            simpa only [g, List.length_map] using b.isLt)))) n
                        ⟨m.val, d.mem_cutoff.mpr ⟨(d.mem_cutoff.mp m.property).1,
                          (d.mem_cutoff.mp m.property).2.trans
                            (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
                        (d.shiftedQuotientComponent ℳ p (p + m.val) k
                          (PositiveDegrees.degree_add_val_sub_self_le d p k m)
                          (field k (hBc.mono (Nat.le_succ k)) (z b))) := by
  classical
  obtain ⟨E, r, hr, hsign, hrec⟩ := exists_backwardRayRecursionArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial k hBc hD hB hout F hs
  refine ⟨E, r, hr, hsign, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hn⟩ := hrec Q hQ
  refine ⟨y, hy, fun n hn' => ?_⟩
  filter_upwards [hn n hn'] with T hT
  obtain ⟨hTpos, htail, x, e, hx, he⟩ := hT
  refine ⟨hTpos, htail, x, e, hx, ?_⟩
  dsimp only at he ⊢
  filter_upwards [he] with δ hδ
  obtain ⟨z, hz, hsum⟩ := hδ
  refine ⟨z, hz, hsum.trans ?_⟩
  apply Finset.sum_congr rfl
  intro b _
  -- The old attached cutoff and the canonical cutoff subtype enumerate the same degrees.
  refine Finset.sum_bij (fun m _ =>
    (⟨m.val, (d.finite_cutoff k).mem_toFinset.mp m.property⟩ : d.cutoff k))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro m _ m' _ h
    exact Subtype.ext (congrArg (fun m : d.cutoff k => m.val) h)
  · intro m _
    exact ⟨⟨m.val, (d.finite_cutoff k).mem_toFinset.mpr m.property⟩,
      Finset.mem_attach _ _, rfl⟩
  intro m _
  have hmn : m.val ≠ n.val := by
    have hm := (d.mem_cutoff.mp
      ((d.finite_cutoff k).mem_toFinset.mp m.property)).2
    intro heq
    rw [heq, hn'] at hm
    omega
  rw [eventBlock_self_apply_of_ne d ℳ p ℒ H h B (k + 1) _ n _ hmn]
  congr 2
  apply congrArg ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ (k + 1))
  -- The signed product of the coincident indexed crossings is the canonical event label.
  refine (List.getElem_map _).trans ?_
  exact B.crossingEventProduct_eq_wallEventLabel (k + 1) e
    (Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e
      (List.mem_reverse.mp (List.getElem_mem (by
        simpa only [List.length_map] using b.isLt))))) _
    ((WallEvent.mem_support _ _ _).mpr fun c =>
      mem_crossingWallEvent _ e _ _ c) (normal_sign_crossingWallEvent _ e _ _)

end Mei.ModuleProbe
