/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.EventInput
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.IncomingGerm
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Straight generic inputs to probe crossing recursions

The transported input before a simultaneous crossing is the actual probe field
on every sufficiently short straight incoming germ with the same incident normal
signs. The germ can follow the degree of an incoming broken line, independently
of the direction of the segment used to compute the crossing product.

For finite families of outgoing and incoming directions, one endpoint arrangement
makes these exact straight cuts generic for a prescribed discriminant. One common
displacement bound works for every event and every compatible incoming direction
on a chosen segment. The arrangement is independent of segment length. This lets
coefficient induction use the same geometric cuts as decorated-ray attachment.

We use `eventually_exists_extendedCoefficientField_eq_eventInput`, the wall-free
germ comparison `eventually_exists_extendedCoefficientField_eq_of_mul_pos`, and
`Convex.exists_forall_eventually_isGeneric_sweepProjection`. For the backward-ray
recursion see Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "labels" k:max e:max => (List.map
  (crossingEventProduct (G := d.truncatedGroup ℒ k)
    (fun c : B.active k => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute k) e) (List.reverse (orderedCrossingTimes e)))
local notation "cutoffRestriction" hkl:max => (WallComplement.restrictPrefunctor
  (fun c : B.active _ => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono hkl)))

/-- The whole suffix-transported probe input can be read on any straight
incoming germ whose strict normal signs agree at the crossing. Only normals of
lower-cutoff walls incident to that point are constrained. The incoming direction
may differ from the segment direction, and the cutoff may be arbitrarily smaller. -/
theorem eventually_exists_extendedCoefficientField_eq_eventInput_of_mul_pos
    {k l : ℕ} (hkl : k ≤ l) (hBc : B.LevelConsistent k)
    {x y : WallComplement (fun c : B.active l => (B.wall c).support)}
    (e : x ⟶ y) (v w : V) {L : ℝ} (hL : 0 < L)
    (hxy : x.val - y.val = L • v)
    (b : Fin (orderedCrossingTimes e).length)
    (hsign : ∀ c : B.active k,
      AffineMap.lineMap x.val y.val
        ((orderedCrossingTimes e).reverse[b.val]'(by
          simpa only [List.length_reverse] using b.isLt)) ∈ (B.wall c).support →
        0 < h.realCharacter (B.wall c).normal v * h.realCharacter (B.wall c).normal w) :
    let τ := (orderedCrossingTimes e).reverse
    let g := labels l e
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∃ z : WallComplement (fun c : B.active k => (B.wall c).support),
        z.val = AffineMap.lineMap x.val y.val
          (τ[b.val]'(by simpa only [τ, List.length_reverse] using b.isLt)) + δ • w ∧
        field k hBc z = (A).truncatedBCHAction d ℒ k
          ((d.truncationMap ℒ hkl).bchGroupMap (g.drop (b.val + 1)).prod)
          (field k hBc ((cutoffRestriction hkl).obj x)) := by
  dsimp only
  let τ := (orderedCrossingTimes e).reverse
  have hb : b.val < τ.length := by simpa only [τ, List.length_reverse] using b.isLt
  let θ := AffineMap.lineMap x.val y.val τ[b.val]
  have hyx : y.val - x.val = -L • v := by rw [← neg_sub x.val y.val, hxy, neg_smul]
  have hsame := eventually_exists_extendedCoefficientField_eq_of_mul_pos
    d ℳ p ℒ H h h' D B k hBc θ v w hsign
  -- Positive normalized ray displacement corresponds to approaching the event
  -- from below in the segment parameter, regardless of the segment length.
  have hlim : Tendsto (fun δ : ℝ => τ[b.val] - δ / L)
      (𝓝[>] 0) (𝓝[<] τ[b.val]) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun δ : ℝ => τ[b.val] - δ / L) (𝓝 0) (𝓝 τ[b.val]) := by
        have hc : ContinuousAt (fun δ : ℝ => τ[b.val] - δ / L) 0 := by fun_prop
        simpa only [zero_div, sub_zero] using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact sub_lt_self _ (div_pos hδ hL)
  have hin := hlim.eventually (eventually_exists_extendedCoefficientField_eq_eventInput
    d ℳ p ℒ H h h' D B hkl hBc e b)
  filter_upwards [hsame, hin] with δ hs hi
  obtain ⟨z₀, z, hz₀, hz, heq⟩ := hs
  obtain ⟨-, w, hw, hinput⟩ := hi
  have hpos : w.val = θ + δ • v := by
    rw [hw, AffineMap.lineMap_apply_module']
    dsimp only [θ]
    rw [AffineMap.lineMap_apply_module']
    rw [hyx, smul_smul, smul_smul]
    field_simp
    module
  have hwz : ((cutoffRestriction hkl).obj w) = z₀ := WallComplement.ext (hpos.trans hz₀.symm)
  exact ⟨z, hz, heq.trans (hwz ▸ hinput)⟩

/-- For finite outgoing and incoming direction families, choose an endpoint
arrangement so that every compatible straight incoming cut at every segment event
is generic and reads the actual lower-cutoff event input. Compatibility asks only
for matching strict normal signs at the incident active walls. A single positive
displacement bound works for all events and compatible directions on that segment.
The arrangement is chosen before its endpoints and length, and no consistency of
the extended probe diagram is needed. -/
theorem exists_straightEventInputArrangement
    {k l : ℕ} (hkl : k ≤ l) (hBc : B.LevelConsistent k)
    (F : ExceptionalArrangement V) {α β : Type*} [Finite α] [Finite β]
    (v : α → V) (w : β → V) :
    ∃ G : ExceptionalArrangement V,
      ∀ (x y : WallComplement (fun c : B.active l => (B.wall c).support)),
        G.IsGeneric y.val → ∀ (e : x ⟶ y) (a : α) (L : ℝ),
        0 < L → x.val - y.val = L • v a →
        let τ := (orderedCrossingTimes e).reverse
        let g := labels l e
        ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ (j : Fin g.length) (b : β),
          (∀ c : B.active l,
            AffineMap.lineMap x.val y.val
              (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∈
                (B.wall c).support →
              0 < h.realCharacter (B.wall c).normal (v a) *
                h.realCharacter (B.wall c).normal (w b)) →
          ∃ z : WallComplement (fun c : B.active k => (B.wall c).support),
            z.val = AffineMap.lineMap x.val y.val
              (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) + δ • w b ∧
            F.IsGeneric z.val ∧
            field k hBc z = (A).truncatedBCHAction d ℒ k
              ((d.truncationMap ℒ hkl).bchGroupMap (g.drop (j.val + 1)).prod)
              (field k hBc ((cutoffRestriction hkl).obj x)) := by
  classical
  let := h.finiteDimensional
  let ν (c : B.active l) := (h.realCharacter (B.wall c).normal).toContinuousLinearMap
  let base (c : B.active l) := (B.wall c).support_nonempty.choose
  let height (c : B.active l) := ν c (base c)
  let I := {t : B.active l × α × β // ν t.1 (w t.2.2) ≠ 0}
  obtain ⟨G, hG⟩ := exists_forall_eventually_isGeneric_sweepProjection F
    (fun t : I => ν t.val.1) (fun t => height t.val.1)
    (fun t => (ν t.val.1 (v t.val.2.1))⁻¹ • v t.val.2.1)
    (fun t => w t.val.2.2) (fun t => t.property)
  refine ⟨G, fun x y hy e a L hL hxy => ?_⟩
  dsimp only
  let τ := (orderedCrossingTimes e).reverse
  let g := labels l e
  -- Every actual event is the hyperplane projection of the endpoint. Its
  -- incoming normal sign selects a transverse member of the finite inventory.
  have hgeneric (j : Fin g.length) (b : β)
      (hsign : ∀ c : B.active l,
        AffineMap.lineMap x.val y.val
          (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∈
            (B.wall c).support → 0 < ν c (v a) * ν c (w b)) :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        F.IsGeneric (AffineMap.lineMap x.val y.val
          (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) + δ • w b) := by
    have hj : j.val < τ.length := by simpa only [g, List.length_map] using j.isLt
    obtain ⟨c, hc⟩ := (mem_orderedCrossingTimes e τ[j.val]).mp
      (List.mem_reverse.mp (List.getElem_mem hj))
    have hmem := (mem_crossings _ _ _ _).mp hc |>.2
    have hv : ν c (v a) ≠ 0 := left_ne_zero_of_mul (ne_of_gt (hsign c hmem))
    have hw : ν c (w b) ≠ 0 := right_ne_zero_of_mul (ne_of_gt (hsign c hmem))
    let t : I := ⟨(c, a, b), hw⟩
    have hh : ν c (AffineMap.lineMap x.val y.val τ[j.val]) = height c :=
      (B.wall c).normal_apply_eq hmem (B.wall c).support_nonempty.choose_spec
    have hpoint : AffineMap.lineMap x.val y.val τ[j.val] =
        sweepProjection (ν c) (height c) ((ν c (v a))⁻¹ • v a) y.val := by
      have hline : AffineMap.lineMap x.val y.val τ[j.val] =
          y.val + ((1 - τ[j.val]) * L) • v a := by
        rw [AffineMap.lineMap_apply_module']
        have hyx : y.val - x.val = -L • v a := by rw [← neg_sub, hxy, neg_smul]
        have hx : x.val = y.val + L • v a :=
          (sub_eq_iff_eq_add.mp hxy).trans (add_comm _ _)
        rw [hyx, hx, smul_smul]
        module
      rw [hline, map_add, map_smul, smul_eq_mul] at hh
      have htime : (height c - ν c y.val) / ν c (v a) = (1 - τ[j.val]) * L := by
        apply (div_eq_iff hv).mpr
        linarith
      rw [hline, sweepProjection_apply, smul_smul, ← div_eq_mul_inv, htime]
    exact (hG y.val hy).mono fun δ hδ => by
      simpa only [t, hpoint] using hδ t
  -- All finite events and directions use one common positive displacement;
  -- directions on the wrong side impose no condition.
  have hinputs (j : Fin g.length) (b : β) :
      ∀ᶠ δ : ℝ in 𝓝[>] 0,
        (∀ c : B.active l,
          AffineMap.lineMap x.val y.val
            (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∈
              (B.wall c).support → 0 < ν c (v a) * ν c (w b)) →
        ∃ z : WallComplement (fun c : B.active k => (B.wall c).support),
          z.val = AffineMap.lineMap x.val y.val
            (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) + δ • w b ∧
          F.IsGeneric z.val ∧
          field k hBc z = (A).truncatedBCHAction d ℒ k
            ((d.truncationMap ℒ hkl).bchGroupMap (g.drop (j.val + 1)).prod)
            (field k hBc ((cutoffRestriction hkl).obj x)) := by
    by_cases hs : ∀ c : B.active l,
        AffineMap.lineMap x.val y.val
          (τ[j.val]'(by simpa only [g, List.length_map] using j.isLt)) ∈
            (B.wall c).support → 0 < ν c (v a) * ν c (w b)
    · have hj : j.val < (orderedCrossingTimes e).length := by
        simpa only [g, List.length_map, List.length_reverse] using j.isLt
      filter_upwards [hgeneric j b hs,
        eventually_exists_extendedCoefficientField_eq_eventInput_of_mul_pos
          d ℳ p ℒ H h h' D B hkl hBc e (v a) (w b) hL hxy ⟨j.val, hj⟩
          (fun c hc => hs ⟨c.val, B.active_mono hkl c.property⟩ hc)] with δ hgen hin _
      obtain ⟨z, hz, heq⟩ := hin
      exact ⟨z, hz, hz ▸ hgen, heq⟩
    · exact Eventually.of_forall fun _ hs' => (hs hs').elim
  exact eventually_all.mpr fun j => eventually_all.mpr (hinputs j)

end Mei.ModuleProbe
