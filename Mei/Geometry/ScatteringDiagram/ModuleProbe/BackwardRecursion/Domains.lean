/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Coherent

/-!
# Compatible domains for the coherent probe recursion

Iterating the actual coherent backward-ray construction gives one generic domain
per retained relative degree. Every compatible preceding read lies in its own
domain. The coefficient field uses one ambient cutoff throughout, while the
geometric event inventory is chosen separately at each output degree.
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


/-- Choose actual backward segments and generic input cuts simultaneously across
all positive output degrees. The ambient probe field is fixed, and each input is
generic for its own strictly earlier degree domain. -/
theorem exists_coherentProbeRecursionDomains
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
    ∃ E : d.cutoff K → ExceptionalArrangement ℝ V,
      (∀ n Q, (E n).IsGeneric Q → A.IsGeneric Q ∧
        ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      ∀ n : d.cutoff K, n.val ≠ 0 → ∀ Q, (E n).IsGeneric Q →
        ∃ (hnK : (d.degree n.val).toNat ≤ K)
          (y : WallComplement (B.activeSupport (d.degree n.val).toNat)), y.val = Q ∧
          ∀ᶠ T : ℝ in atTop, 0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (d.degree n.val).toNat,
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (B.activeSupport (d.degree n.val).toNat)) (e : x ⟶ y),
              x.val = Q + T • i (ρ (p + n.val)) ∧
              ∀ᶠ δ : ℝ in 𝓝[>] 0,
                (∀ b ∈ segmentWallEvents (B.activeNormal (d.degree n.val).toNat) e,
                  ∀ m : d.cutoff (d.degree n.val).toNat, d.Precedes m.val n.val →
                    b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
                      b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val))) →
                    (E ⟨m.val, d.cutoff_mono hnK m.property⟩).IsGeneric
                      (Q + segmentEventParameter (B.activeNormal (d.degree n.val).toNat) e T b •
                        i (ρ (p + n.val)) + δ • i (ρ (p + m.val)))) ∧
                coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
                  (d.degree n.val).toNat K hnK hBc Q (d.degreeCutoffIndex n) =
                  eventEndpointStep d ℳ p ℒ H h B _ _ (Nat.le_refl _)
                    (fun _ _ => segmentWallEvents (B.activeNormal (d.degree n.val).toNat) e)
                    (fun b X r m => X +
                      segmentEventParameter (B.activeNormal (d.degree n.val).toNat) e T b •
                        i (ρ (p + r.val)) + δ • i (ρ (p + m.val)))
                    (coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
                      (d.degree n.val).toNat K hnK hBc) Q (d.degreeCutoffIndex n) := by
  classical
  let := h.finiteDimensional
  obtain ⟨S, hS⟩ := exists_ray_admissibilityArrangement
    (fun c : B.active K => (B.wall c).support)
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) (∅ : Finset V)
  have hallowed (Q : V) (hQ : S.IsGeneric Q) :
      ∀ c : B.active K, Q ∉ (B.wall c).support := by
    obtain ⟨y, hy, _⟩ := hS Q hQ
    exact hy ▸ y.notMem
  let stepProperty (j : ℕ) (hjK : j ≤ K)
      (F G : ExceptionalArrangement ℝ V) : Prop :=
    let f := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
      j K hjK hBc;
      (∀ Q, G.IsGeneric Q → ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
      ∀ Q, G.IsGeneric Q →
        ∃ y : WallComplement (B.activeSupport j), y.val = Q ∧
          ∀ n : d.cutoff j, d.degree n.val = j →
            ∀ᶠ T : ℝ in atTop, 0 < T ∧
              (∀ s ≥ T, ∀ c : B.active j,
                Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
              ∃ (x : WallComplement (B.activeSupport j)) (e : x ⟶ y),
                x.val = Q + T • i (ρ (p + n.val)) ∧
                ∀ᶠ δ : ℝ in 𝓝[>] 0,
                  (∀ b ∈ segmentWallEvents (B.activeNormal j) e,
                    ∀ m : d.cutoff j,
                      b.normal (B.activeNormal j) (i (ρ (p + n.val))) =
                        b.normal (B.activeNormal j) (i (ρ (p + m.val))) →
                      let Z := Q +
                        segmentEventParameter (B.activeNormal j) e T b •
                          i (ρ (p + n.val)) + δ • i (ρ (p + m.val))
                      F.IsGeneric Z ∧ ∀ c : B.active K, Z ∉ (B.wall c).support) ∧
                  f Q n =
                    eventEndpointStep d ℳ p ℒ H h B j j (Nat.le_refl _)
                      (fun _ _ => segmentWallEvents (B.activeNormal j) e)
                      (fun b X r m => X +
                        segmentEventParameter (B.activeNormal j) e T b •
                          i (ρ (p + r.val)) + δ • i (ρ (p + m.val))) f Q n
  have hstep (j : ℕ) (hj : 0 < j) (hjK : j ≤ K) (F : ExceptionalArrangement ℝ V) :
      ∃ G, stepProperty j hjK F G := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    exact exists_coherentBackwardRayEndpointStepArrangement d ℳ p ℒ H h h' D₀ a D B
      hinitial k K hjK hBc hD hB
      (fun n _ b hb hray => hout ⟨n.val, d.cutoff_mono hjK n.property⟩ b
        (D.active_mono (by omega) hb) hray) F
  let next (j : ℕ) (hj : 0 < j) (hjK : j ≤ K) (F : ExceptionalArrangement ℝ V) :=
    (hstep j hj hjK F).choose
  have hnext (j : ℕ) (hj : 0 < j) (hjK : j ≤ K) (F : ExceptionalArrangement ℝ V) :=
    (hstep j hj hjK F).choose_spec
  let domains : ℕ → ExceptionalArrangement ℝ V := Nat.rec (A.union S)
    (fun j F => if hjK : j + 1 ≤ K then F.union (next (j + 1) (Nat.succ_pos j) hjK F) else F)
  have hdomains (j l : ℕ) (hjl : j ≤ l) (Q : V)
      (hQ : (domains l).IsGeneric Q) : (domains j).IsGeneric Q := by
    induction l, hjl using Nat.le_induction with
    | base => exact hQ
    | succ l hjl ih =>
      -- Expand one successor of the local Nat.rec arrangement sequence.
      change (if hlK : l + 1 ≤ K then (domains l).union
        (next (l + 1) (Nat.succ_pos l) hlK (domains l)) else domains l).IsGeneric Q at hQ
      split_ifs at hQ with hlK
      · exact ih (ExceptionalArrangement.isGeneric_union.mp hQ).1
      · exact ih hQ
  refine ⟨fun n => domains (d.degree n.val).toNat, ?_, ?_⟩
  · intro n Q hQ
    have hzero := hdomains 0 _ (Nat.zero_le _) Q hQ
    exact ⟨(ExceptionalArrangement.isGeneric_union.mp hzero).1,
      hallowed Q (ExceptionalArrangement.isGeneric_union.mp hzero).2⟩
  · intro n hn Q hQ
    have hnpos := d.degree_pos (d.mem_cutoff.mp n.property).1 hn
    have hnK : (d.degree n.val).toNat ≤ K := by
      have hbound := (d.mem_cutoff.mp n.property).2
      omega
    have hs : (d.degree n.val).toNat - 1 + 1 = (d.degree n.val).toNat := by omega
    have hprev : (d.degree n.val).toNat - 1 + 1 ≤ K := by omega
    have hnNat : 0 < (d.degree n.val).toNat := by omega
    have houtQ : (next (d.degree n.val).toNat hnNat hnK
        (domains ((d.degree n.val).toNat - 1))).IsGeneric Q := by
      dsimp only at hQ
      rw [← hs] at hQ
      -- Expand the same local recursion at this positive output degree.
      change (if hh : (d.degree n.val).toNat - 1 + 1 ≤ K then
        (domains ((d.degree n.val).toNat - 1)).union
          (next _ (Nat.succ_pos _) hh (domains ((d.degree n.val).toNat - 1)))
        else domains ((d.degree n.val).toNat - 1)).IsGeneric Q at hQ
      rw [dite_eq_left hprev] at hQ
      simpa only [Nat.succ_eq_add_one, hs] using (ExceptionalArrangement.isGeneric_union.mp hQ).2
    have hrec := (hnext _ hnNat hnK (domains ((d.degree n.val).toNat - 1))).2 Q houtQ
    obtain ⟨y, hy, hrec⟩ := hrec
    refine ⟨hnK, y, hy, ?_⟩
    have hn' : d.degree (d.degreeCutoffIndex n).val = ((d.degree n.val).toNat : ℤ) := by
      rw [PositiveDegrees.degreeCutoffIndex_val]
      omega
    filter_upwards [hrec (d.degreeCutoffIndex n) hn'] with T hT
    obtain ⟨hT, htail, x, e, hx, hcuts⟩ := hT
    refine ⟨hT, htail, x, e, hx, ?_⟩
    filter_upwards [hcuts] with δ hδ
    refine ⟨?_, hδ.2⟩
    intro b hb m hmn hnormal
    apply hdomains _ ((d.degree n.val).toNat - 1) _ _ ((hδ.1 b hb m hnormal).1)
    have hmnonneg := d.degree_nonneg (d.mem_cutoff.mp m.property).1
    have hmdegree := d.degree_lt_of_precedes hmn
    omega

end Mei.ModuleProbe
