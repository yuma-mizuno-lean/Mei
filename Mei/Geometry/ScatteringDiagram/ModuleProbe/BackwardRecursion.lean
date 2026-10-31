/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Asymptotic.Extension
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.EventInput
public import Mei.Geometry.Convex.Polyhedron.Path.Ray

/-!
# The probe recursion along complete backward rays

At a generic endpoint, the probe component of positive relative degree is the
sum of the crossing contributions on its backward ray. A sufficiently long
admissible segment contains every encounter on that half-ray and starts where
the component has its prescribed incoming value, which is zero in positive
relative degree. Each contribution reads whole coefficients at the preceding
cutoff, at actual incoming points arbitrarily close to its simultaneous event.
The proximity bound is in the ray parameter, independently of segment length.

The finite arrangement works simultaneously for every degree of a given order.
Coincident indexed walls remain one combined event, and no commutation between
different events is assumed. Zero spatial directions and empty event lists are
included. Only additional probe walls carrying the component in question must
be outgoing.

We assemble `Convex.exists_ray_admissibilityArrangement`,
`ModuleProbe.eventually_shiftedQuotientComponent_extendedCoefficientField_eq`
and `ModuleProbe.exists_shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_eventInputs`.
The backward-ray recursion follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ κ' : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

local notation "A" => d.shiftedLieFiltration ℒ ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "labels" k:max e:max => (List.map
  (crossingEventProduct (G := d.truncatedGroup ℒ k)
    (fun c : B.active k => h.realCharacter
      (DirectedWall.normal (DirectedDiagram.wall B c)))
    (fun c => CompletedGroup.projection k (DirectedWall.label (DirectedDiagram.wall B c)))
    (B.activeLabels_commute k) e)
      (List.reverse (orderedCrossingTimes e)))
local notation "restriction" k:max => (WallComplement.restrictPrefunctor
  (fun c : B.active (k + 1) => DirectedWall.support (DirectedDiagram.wall B c))
  (Set.inclusion (B.active_mono (Nat.le_succ k))))

/-- One arrangement gives the positive-degree backward-ray recursion for every
retained degree of order `k + 1`. All sufficiently long segments contain every
backward encounter: the entire ray beyond their starting point misses all active
walls. For any positive ray-parameter tolerance, the finite sum reads lower-order
probe values at incoming points within that tolerance of each crossing.

The output degree is `p + n`; the sum uses relative input degrees at most `k`.
The crossing list is in multiplication order, with the first crossing rightmost.
No nonzero spatial direction or coefficient-basis hypothesis is required. -/
theorem exists_backwardRayRecursionArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hBc : B.LevelConsistent (k + 1))
    (hD : D.LevelConsistent (k + 2))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) (k + 1))
    (hout : ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
      ∀ b, Sum.inr b ∈ D.active (k + 2) →
        (p + n.val, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
          (D.wall (.inr b)).Outgoing) :
    ∃ E : ExceptionalArrangement V, ∀ Q, E.IsGeneric Q →
      ∃ y : WallComplement (fun c : B.active (k + 1) => (B.wall c).support),
        y.val = Q ∧ ∀ n : d.cutoff (k + 1), d.degree n.val = k + 1 →
          ∀ᶠ T : ℝ in atTop, 0 < T ∧
            (∀ s ≥ T, ∀ c : B.active (k + 1),
              Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support) ∧
            ∃ (x : WallComplement (fun c : B.active (k + 1) => (B.wall c).support))
              (e : x ⟶ y), x.val = Q + T • i (ρ (p + n.val)) ∧
              let τ := (orderedCrossingTimes e).reverse
              let g := labels (k + 1) e
              ∀ ε : ℝ, 0 < ε →
                ∃ (t : Fin g.length → ℝ)
                  (z : Fin g.length →
                    WallComplement (fun c : B.active (k + 1) => (B.wall c).support)),
                  (∀ j : Fin g.length,
                    t j ∈ Ioo (0 : ℝ) (τ[j.val]'(by
                      simpa only [g, List.length_map] using j.isLt)) ∧
                    T * (τ[j.val]'(by
                      simpa only [g, List.length_map] using j.isLt) - t j) < ε ∧
                    (z j).val = Q + ((1 - t j) * T) • i (ρ (p + n.val))) ∧
                  d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
                    (by simpa only [add_sub_cancel_left] using
                      (d.mem_cutoff.mp n.property).2) (field (k + 1) hBc y) =
                    ∑ j : Fin g.length, ∑ m ∈ (d.finite_cutoff k).toFinset.attach,
                      d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1)
                        (by simpa only [add_sub_cancel_left] using
                          (d.mem_cutoff.mp n.property).2)
                        ((A).truncatedBCHAction d ℒ (k + 1) g[j]
                          (Submodule.Quotient.mk
                            (shiftedInclusion ℳ d.monoid p
                              ⟨m.val, (d.mem_cutoff.mp
                                ((d.finite_cutoff k).mem_toFinset.mp m.property)).1⟩
                              (d.shiftedQuotientComponent ℳ p (p + m.val) k
                                (by simpa only [add_sub_cancel_left] using
                                  (d.mem_cutoff.mp
                                    ((d.finite_cutoff k).mem_toFinset.mp m.property)).2)
                                (field k (hBc.mono (Nat.le_succ k))
                                  ((restriction k).obj (z j))))))) := by
  classical
  let := h.finiteDimensional
  -- The geometric arrangement works for the whole finite degree inventory.
  let vectors := (d.finite_cutoff (k + 1)).toFinset.image (fun n => i (ρ (p + n)))
  obtain ⟨E, hE⟩ := exists_ray_admissibilityArrangement
    (fun c : B.active (k + 1) => (B.wall c).support)
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) vectors
  refine ⟨E, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hsegment⟩ := hE Q hQ
  refine ⟨y, hy, fun n hn => ?_⟩
  have hv : i (ρ (p + n.val)) ∈ vectors :=
    Finset.mem_image.mpr ⟨n.val, (d.finite_cutoff (k + 1)).mem_toFinset.mpr n.property, rfl⟩
  -- Eventual admissibility also excludes every encounter beyond the starting point.
  have htail : ∀ᶠ T : ℝ in atTop, ∀ s ≥ T, ∀ c : B.active (k + 1),
      Q + s • i (ρ (p + n.val)) ∉ (B.wall c).support :=
    (eventually_forall_ge_atTop.mpr (hsegment _ hv)).mono fun T hT s hs c hmem => by
      obtain ⟨x, hx, _⟩ := hT s hs
      exact x.notMem c (hx ▸ hmem)
  have hq : d.degree ((p + n.val) - p) = k + 1 := by
    simpa only [add_sub_cancel_left] using hn
  have hne : p ≠ p + n.val := by
    intro he
    rw [← he, sub_self, map_zero] at hq
    omega
  filter_upwards [eventually_gt_atTop (0 : ℝ), htail, hsegment _ hv,
    eventually_shiftedQuotientComponent_extendedCoefficientField_eq
      d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB (p + n.val)
      (by omega) (hout n hn) (isCompact_singleton (x := Q))] with T hT htail hseg hvalue
  obtain ⟨x, hx, he⟩ := hseg
  let e : x ⟶ y := ⟨he⟩
  -- The distant initial component vanishes because the output has positive relative degree.
  have hzero : d.shiftedQuotientComponent ℳ p (p + n.val) (k + 1) (by omega)
      (field (k + 1) hBc x) = 0 := by
    have hx' : (⟨Q + T • i (ρ (p + n.val)), by rw [← hx]; exact x.notMem⟩ :
        WallComplement (fun c : B.active (k + 1) => (B.wall c).support)) = x :=
      WallComplement.ext hx.symm
    have hv := hvalue Q (mem_singleton Q) (by rw [← hx]; exact x.notMem)
    rw [hx'] at hv
    exact hv.trans (Subtype.ext (DirectSum.decompose_of_mem_ne ℳ a.property hne))
  refine ⟨hT, htail, x, e, hx, ?_⟩
  dsimp only
  intro ε hε
  obtain ⟨t, z, hz, hsum⟩ :=
    exists_shiftedQuotientComponent_extendedCoefficientField_eq_add_sum_eventInputs
      d ℳ p ℒ H h h' D B k hBc hD hB e (p + n.val) hq (div_pos hε hT)
  refine ⟨t, z, fun j => ⟨(hz j).1, ?_, ?_⟩, ?_⟩
  · simpa only [mul_comm] using (lt_div_iff₀ hT).mp ((hz j).2.1)
  · rw [(hz j).2.2, hx, hy, AffineMap.lineMap_apply_module']
    module
  · simpa only [hzero, zero_add] using hsum

end Mei.ModuleProbe
