/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Asymptotic
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension

/-!
# Incoming values of extended probe coefficients

The asymptotic incoming condition holds at every endpoint off the active base
walls, uniformly for starting points in a compact set. No auxiliary probe
arrangement needs to be avoided. In particular, a component with zero spatial
direction has its incoming value at every allowed endpoint, both in the finite
quotients and in the completed shifted module. These are the initial conditions
for the coefficient recursion along backward rays.

We extend `eventually_shiftedQuotientComponent_coefficientField_eq` using
`isLocallyConstant_extendedCoefficientField` and the density of generic points.
A compact thickening keeps the asymptotic bound uniform while moving an endpoint
to a nearby generic point. The interpretation follows Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

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

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B

/-- Far along a degree's positive spatial direction, its retained component in
the extended probe field equals its incoming value. The bound is uniform over
compact sets of starting points, and the translated endpoint need only avoid the
active base walls. Only additional active walls carrying this degree must be
outgoing. -/
theorem eventually_shiftedQuotientComponent_extendedCoefficientField_eq
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1)) (hBc : B.LevelConsistent k)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (q : Γ) (hk : d.degree (q - p) ≤ k)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ Q ∈ K,
      ∀ hQ : ∀ c : B.active k, Q + t • i (ρ q) ∉ (B.wall c).support,
      d.shiftedQuotientComponent ℳ p q k hk
        (field k hBc ⟨Q + t • i (ρ q), hQ⟩) =
        DirectSum.decompose ℳ (a : M) q := by
  let := h.finiteDimensional
  have hopen : IsOpen {x : V | ∀ c : B.active k, x ∉ (B.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using
      isOpen_iInter_of_finite
        (fun c : B.active k => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  have hdense : Dense {x : {x : V // ∀ c : B.active k, x ∉ (B.wall c).support} |
      (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val} :=
    (coefficientArrangement d ℳ p ℒ H h h' D k).dense_isGeneric.preimage
      hopen.isOpenMap_subtype_val
  filter_upwards [eventually_shiftedQuotientComponent_coefficientField_eq
    d ℳ p ℒ H h h' D₀ a D hinitial k hD q hk hout (hK.cthickening (r := 1))]
    with t ht Q hQK hQ
  let x : {x : V // ∀ c : B.active k, x ∉ (B.wall c).support} :=
    ⟨Q + t • i (ρ q), hQ⟩
  obtain ⟨U, hU, hxU, hlocal⟩ :=
    (isLocallyConstant_extendedCoefficientField d ℳ p ℒ H h h' D B k hBc).exists_open x
  obtain ⟨z, ⟨hzU, hdist⟩, hz⟩ := hdense.inter_open_nonempty
    (U ∩ Subtype.val ⁻¹' Metric.ball x.val 1)
    (hU.inter (Metric.isOpen_ball.preimage continuous_subtype_val))
    ⟨x, hxU, by simp⟩
  simp only [mem_ofPred_eq] at hz
  have hzK : z.val - t • i (ρ q) ∈ Metric.cthickening 1 K := by
    apply Metric.mem_cthickening_of_dist_le _ Q 1 K hQK
    calc
      dist (z.val - t • i (ρ q)) Q = dist z.val (Q + t • i (ρ q)) := by
        simpa only [add_sub_cancel_right] using
          dist_sub_right z.val (Q + t • i (ρ q)) (t • i (ρ q))
      _ ≤ 1 := (Metric.mem_ball.mp hdist).le
  have hvalue := ht (z.val - t • i (ρ q)) hzK
    (by simpa only [sub_add_cancel] using hz)
  simp only [sub_add_cancel] at hvalue
  have hext := extendedCoefficientField_eq_coefficientField
    d ℳ p ℒ H h h' D B k hBc hD hB ⟨z.val, z.property⟩ hz
  rw [← hext, hlocal z hzU] at hvalue
  exact hvalue

/-- A retained component with zero spatial direction has its incoming value at
every allowed base endpoint. The auxiliary probe arrangement imposes no
restriction on that endpoint. -/
theorem shiftedQuotientComponent_extendedCoefficientField_eq_of_spatial_eq_zero
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1)) (hBc : B.LevelConsistent k)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (q : Γ) (hk : d.degree (q - p) ≤ k) (hq : i (ρ q) = 0)
    (hout : ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    d.shiftedQuotientComponent ℳ p q k hk (field k hBc x) =
      DirectSum.decompose ℳ (a : M) q := by
  obtain ⟨t, ht⟩ := (eventually_shiftedQuotientComponent_extendedCoefficientField_eq
    d ℳ p ℒ H h h' D₀ a D B hinitial k hD hBc hB q hk hout
    (isCompact_singleton (x := x.val))).exists
  simpa only [hq, smul_zero, add_zero] using
    ht x.val (mem_singleton x.val) (by simpa only [hq, smul_zero, add_zero] using x.notMem)

/-- In the completed probe field, every zero-spatial-direction component equals
the corresponding incoming component at every all-order allowed endpoint. -/
theorem shiftedHomogeneousComponent_completedExtendedCoefficientField_eq_of_spatial_eq_zero
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (q : Γ) (hq : i (ρ q) = 0)
    (hout : ∀ k b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    (x : B.Point) :
    d.shiftedHomogeneousComponent ℳ p q
        (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) =
      DirectSum.decompose ℳ (a : M) q := by
  let k := (d.degree (q - p)).toNat
  rw [d.shiftedHomogeneousComponent_eq ℳ p q k (Int.self_le_toNat _),
    projection_completedExtendedCoefficientField]
  exact shiftedQuotientComponent_extendedCoefficientField_eq_of_spatial_eq_zero
    d ℳ p ℒ H h h' D₀ a D B hinitial k ((D.consistent_iff.mp hD) (k + 1))
    ((B.consistent_iff.mp hBc) k) ((DirectedDiagram.equivalent_iff _ _).mp hB k)
    q (Int.self_le_toNat _) hq (hout k) _

end Mei.ModuleProbe
