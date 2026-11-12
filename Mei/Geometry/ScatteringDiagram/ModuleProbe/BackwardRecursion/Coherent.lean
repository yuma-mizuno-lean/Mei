/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Endpoint

/-!
# Probe recursions in a common coefficient cutoff

The backward endpoint recurrence originally reads actual probe components at the
preceding cutoff. Here both its input and output are read from the actual probe
field at any common larger cutoff. Generic straight input cuts avoid that larger
active-wall family, and transition compatibility identifies every contributing
lower component. No relation between the independently chosen generic anchors
is assumed.

The event inventory remains at the output degree's cutoff. This is a coefficient
coherence supplier for the probe/ray comparison, not a comparison of different
geometric event inventories or a final identification with decorated rays.
The backward-ray interpretation follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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

section ArbitraryProbe

variable {σ : Type*}
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) σ)
  (B : DirectedDiagram (d := d) h H κ')

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)

open Classical in
/-- Actual probe components at a common larger cutoff, extended by zero only
outside its active-wall complement. -/
def coherentProbeEndpointFunction (k K : ℕ) (hkK : k ≤ K)
    (hBc : B.LevelConsistent K) :
    PositiveDegrees.ShiftedEndpointFunction d ℳ p V k := fun Q n =>
  if hQ : ∀ c : B.active K, Q ∉ (B.wall c).support then
    d.shiftedQuotientComponent ℳ p (p + n.val) K
      ((PositiveDegrees.degree_add_val_sub_self_le d p k n).trans
        (Int.ofNat_le.mpr hkK)) (field K hBc ⟨Q, hQ⟩)
  else 0

open Classical in
/-- The coherent endpoint function reads the actual larger-cutoff component on
its allowed locus and is zero elsewhere. -/
theorem coherentProbeEndpointFunction_def (k K : ℕ) (hkK : k ≤ K)
    (hBc : B.LevelConsistent K) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc = fun Q n =>
      if hQ : ∀ c : B.active K, Q ∉ (B.wall c).support then
        d.shiftedQuotientComponent ℳ p (p + n.val) K
          ((PositiveDegrees.degree_add_val_sub_self_le d p k n).trans
            (Int.ofNat_le.mpr hkK)) (field K hBc ⟨Q, hQ⟩)
      else 0 := by rfl

/-- At an allowed endpoint, read the larger-cutoff component directly. No
consistency or charge-zero comparison hypothesis on the probe is needed. -/
@[simp]
theorem coherentProbeEndpointFunction_apply_of_allowed
    (k K : ℕ) (hkK : k ≤ K) (hBc : B.LevelConsistent K)
    (Q : V) (n : d.cutoff k) (hQ : ∀ c : B.active K, Q ∉ (B.wall c).support) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc Q n =
      d.shiftedQuotientComponent ℳ p (p + n.val) K
        ((PositiveDegrees.degree_add_val_sub_self_le d p k n).trans
          (Int.ofNat_le.mpr hkK)) (field K hBc ⟨Q, hQ⟩) := by
  simp only [coherentProbeEndpointFunction_def]
  rw [dite_eq_left hQ]

/-- Outside the larger-cutoff allowed locus, all totalized coefficients vanish. -/
theorem coherentProbeEndpointFunction_apply_of_not_allowed
    (k K : ℕ) (hkK : k ≤ K) (hBc : B.LevelConsistent K)
    (Q : V) (n : d.cutoff k) (hQ : ¬ ∀ c : B.active K, Q ∉ (B.wall c).support) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc Q n = 0 := by
  simp only [coherentProbeEndpointFunction_def, hQ, ↓reduceDIte]

/-- The zero branch in simp normal form: a wall containing the point has a
nonidentity projected label, so it is active at the ambient cutoff. -/
@[simp]
theorem coherentProbeEndpointFunction_apply_of_active_wall
    (k K : ℕ) (hkK : k ≤ K) (hBc : B.LevelConsistent K)
    (Q : V) (n : d.cutoff k)
    (hQ : ∃ c, CompletedGroup.projection K (B.wall c).label ≠ 1 ∧ Q ∈ (B.wall c).support) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc Q n = 0 := by
  apply coherentProbeEndpointFunction_apply_of_not_allowed d ℳ p ℒ H h h' D B
    k K hkK hBc Q n
  obtain ⟨c, hc, hQc⟩ := hQ
  intro hallowed
  exact hallowed ⟨c, (B.mem_active K c).mpr hc⟩ hQc

/-- A point on any active larger-cutoff wall has zero totalized coefficients. -/
theorem coherentProbeEndpointFunction_apply_of_mem_support
    (k K : ℕ) (hkK : k ≤ K) (hBc : B.LevelConsistent K)
    (Q : V) (n : d.cutoff k) (c : B.active K) (hQ : Q ∈ (B.wall c).support) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc Q n = 0 := by
  exact coherentProbeEndpointFunction_apply_of_not_allowed d ℳ p ℒ H h h' D B
    k K hkK hBc Q n (fun hQ' => hQ' c hQ)

/-- Enlarging the retained degree index at a fixed ambient cutoff does not
change any retained endpoint coefficient, including on the zero-totalized locus. -/
theorem coherentProbeEndpointFunction_cutoff_inclusion
    {k l K : ℕ} (hkl : k ≤ l) (hlK : l ≤ K) (hBc : B.LevelConsistent K)
    (Q : V) (n : d.cutoff k) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B l K hlK hBc Q
        ⟨n.val, d.cutoff_mono hkl n.property⟩ =
      coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K (hkl.trans hlK) hBc Q n := by
  rw [coherentProbeEndpointFunction_def, coherentProbeEndpointFunction_def]

/-- At a larger-cutoff allowed endpoint, the coherent endpoint function is the
actual lower-cutoff probe component. Anchor choices disappear by probe transport
and coefficient transition compatibility. -/
theorem coherentProbeEndpointFunction_eq_component
    (k K : ℕ) (hkK : k ≤ K) (hBc : B.LevelConsistent K)
    (hD : D.LevelConsistent (K + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) K)
    (z : WallComplement (B.activeSupport K)) (n : d.cutoff k) :
    coherentProbeEndpointFunction d ℳ p ℒ H h h' D B k K hkK hBc z.val n =
      (component k n) (field k (hBc.mono hkK)
        ((WallComplement.restrictPrefunctor (B.activeSupport K)
          (Set.inclusion (B.active_mono hkK))).obj z)) := by
  rw [coherentProbeEndpointFunction_apply_of_allowed d ℳ p ℒ H h h' D B
    k K hkK hBc z.val n z.notMem]
  rw [← transition_extendedCoefficientField d ℳ p ℒ H h h' D B hkK
    (hBc.mono hkK) hBc hD hB,
    d.shiftedQuotientComponent_transition]

end ArbitraryProbe

variable (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)

/-- The actual probe field at any common larger cutoff satisfies the backward
endpoint recurrence at each highest retained positive degree. All normal-compatible
incoming cuts avoid both a prescribed arrangement and the larger active-wall
family. The event inventory and geometric segments stay at cutoff `k + 1`. -/
theorem exists_coherentBackwardRayEndpointStepArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k K : ℕ) (hkK : k + 1 ≤ K) (hBc : B.LevelConsistent K)
    (hD : D.LevelConsistent (K + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) K)
    (hout : ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
      ∀ b, Sum.inr b ∈ D.active (k + 2) →
        (p + n.val, 1) ∈ (D.wall (.inr b)).ray.rayDegrees →
          (D.wall (.inr b)).Outgoing)
    (F : ExceptionalArrangement V) :
    let f := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
      (k + 1) K hkK hBc
    ∃ G : ExceptionalArrangement V,
      (∀ Q, G.IsGeneric Q → ∀ c : B.active K, Q ∉ (B.wall c).support) ∧
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
                      let Z := Q +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + n.val)) + δ • i (ρ (p + m.val))
                      F.IsGeneric Z ∧ ∀ c : B.active K, Z ∉ (B.wall c).support) ∧
                  f Q n =
                    eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
                      (fun _ _ => segmentWallEvents (B.activeNormal (k + 1)) e)
                      (fun b X r m => X +
                        segmentEventParameter (B.activeNormal (k + 1)) e T b •
                          i (ρ (p + r.val)) + δ • i (ρ (p + m.val))) f Q n := by
  classical
  dsimp only
  let := h.finiteDimensional
  obtain ⟨A, hA⟩ := exists_ray_admissibilityArrangement
    (fun c : B.active K => (B.wall c).support)
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) (∅ : Finset V)
  have hallowed (Q : V) (hQ : A.IsGeneric Q) :
      ∀ c : B.active K, Q ∉ (B.wall c).support := by
    obtain ⟨y, hy, _⟩ := hA Q hQ
    exact hy ▸ y.notMem
  obtain ⟨G, g, hg, hG⟩ := exists_backwardRayEndpointStepArrangement
    d ℳ p ℒ H h h' D₀ a D B hinitial k (hBc.mono hkK)
    (hD.mono (by omega)) (hB.mono hkK) hout (F.union A)
  let f := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
    (k + 1) K hkK hBc
  refine ⟨G.union A, fun Q hQ => hallowed Q
    (ExceptionalArrangement.isGeneric_union.mp hQ).2, fun Q hQ => ?_⟩
  obtain ⟨hQG, hQA⟩ := ExceptionalArrangement.isGeneric_union.mp hQ
  obtain ⟨y, hy, hyrec⟩ := hG Q hQG
  have houtput (n : d.cutoff (k + 1)) :
      f Q n = (component (k + 1) n) (field (k + 1) (hBc.mono hkK) y) := by
    have he := coherentProbeEndpointFunction_eq_component d ℳ p ℒ H h h' D B
      (k + 1) K hkK hBc hD hB ⟨Q, hallowed Q hQA⟩ n
    have hy' : ((WallComplement.restrictPrefunctor (B.activeSupport K)
        (Set.inclusion (B.active_mono hkK))).obj ⟨Q, hallowed Q hQA⟩) = y :=
      WallComplement.ext hy.symm
    simpa only [hy'] using he
  dsimp only [f] at houtput
  refine ⟨y, hy, fun n hn => ?_⟩
  filter_upwards [hyrec n hn] with T hT
  obtain ⟨hT, htail, x, e, hx, hrec⟩ := hT
  refine ⟨hT, htail, x, e, hx, ?_⟩
  filter_upwards [hrec] with δ hδ
  refine ⟨fun b hb m hm => ⟨(ExceptionalArrangement.isGeneric_union.mp
    (hδ.1 b hb m hm)).1, hallowed _ (ExceptionalArrangement.isGeneric_union.mp
    (hδ.1 b hb m hm)).2⟩, ?_⟩
  rw [houtput n, hδ.2]
  rw [eventEndpointStep_apply_sum_cutoff, eventEndpointStep_apply_sum_cutoff]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  split_ifs with hv
  · congr 1
    let m' : d.cutoff (k + 1) := ⟨m.val, d.mem_cutoff.mpr
      ⟨(d.mem_cutoff.mp m.property).1,
        (d.mem_cutoff.mp m.property).2.trans (Int.ofNat_le.mpr (Nat.le_succ k))⟩⟩
    let Z := Q + segmentEventParameter (B.activeNormal (k + 1)) e T b •
      i (ρ (p + n.val)) + δ • i (ρ (p + m.val))
    have hZ : ∀ c : B.active K, Z ∉ (B.wall c).support :=
      hallowed Z (ExceptionalArrangement.isGeneric_union.mp (hδ.1 b hb m' hv)).2
    let z : WallComplement (B.activeSupport K) := ⟨Z, hZ⟩
    let zlow := ((WallComplement.restrictPrefunctor (B.activeSupport K)
      (Set.inclusion (B.active_mono ((Nat.le_succ k).trans hkK)))).obj z)
    have hg' := hg zlow m
    have hf' := coherentProbeEndpointFunction_eq_component d ℳ p ℒ H h h' D B
      k K ((Nat.le_succ k).trans hkK) hBc hD hB z m
    -- Expand only the local names for the incoming point and retained index here.
    -- The change of cutoff is performed explicitly by the public lemma below.
    change g Z m' = coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
      (k + 1) K hkK hBc Z m'
    rw [coherentProbeEndpointFunction_cutoff_inclusion d ℳ p ℒ H h h' D B
      (Nat.le_succ k) hkK hBc Z m]
    exact hg'.trans hf'.symm
  · rfl

end Mei.ModuleProbe
