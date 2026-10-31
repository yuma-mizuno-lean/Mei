/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Asymptotic.Extension

/-!
# The incoming coefficient in the leading probe component

The relative-degree-zero component of the probe field is the whole incoming
coefficient at every allowed endpoint. This holds for arbitrary spatial velocity,
including nonzero velocity, and at every finite cutoff and in the completion.
It supplies the initial degree in comparisons of probe coefficients with
weighted broken-line sums. No endpoint genericity is required.

Only additional probe walls carrying the incoming degree at extended order one
must be outgoing. Higher-degree walls do not enter the leading component.
The order-zero base group is trivial, so its field is constant; the asymptotic
incoming condition determines this constant. Cutoff compatibility then recovers
the leading component at every order.

We use `ModuleProbe.eventually_shiftedQuotientComponent_extendedCoefficientField_eq`,
`ModuleProbe.transition_extendedCoefficientField`, and the shifted homogeneous
component API. The probe interpretation follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3
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

local notation "F" => d.shiftedFiltration ℳ p
local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B

/-- At every finite cutoff and allowed endpoint, the leading probe component is
the incoming coefficient. Only outgoingness at extended order one is used;
the spatial direction of the incoming degree is unrestricted. -/
theorem shiftedQuotientComponent_extendedCoefficientField_self
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1)) (hBc : B.LevelConsistent k)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hout : ∀ b, Sum.inr b ∈ D.active 1 →
      (p, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
        (D.wall (.inr b)).Outgoing)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    d.shiftedQuotientComponent ℳ p p k (by simp) (field k hBc x) = a := by
  let hB0 := hBc.mono (Nat.zero_le k)
  let x₀ := (WallComplement.restrictPrefunctor
    (fun c : B.active k => (B.wall c).support)
    (Set.inclusion (B.active_mono (Nat.zero_le k)))).obj x
  have hfar := eventually_shiftedQuotientComponent_extendedCoefficientField_eq
    d ℳ p ℒ H h h' D₀ a D B hinitial 0
    (hD.mono (by omega)) hB0 (hB.mono (Nat.zero_le k)) p (by simp) hout
    (isCompact_singleton (x := x.val))
  obtain ⟨T, hT⟩ := hfar.exists
  have hallowed : ∀ c : B.active 0,
      x.val + T • i (ρ p) ∉ (B.wall c).support := by
    intro c
    apply False.elim
    apply (B.mem_active 0 c.val).mp c.property
    rw [d.groupTower_obj_one]
    exact Subsingleton.elim (α := d.truncatedGroup ℒ 0) _ _
  let z : WallComplement (fun c : B.active 0 => (B.wall c).support) :=
    ⟨x.val + T • i (ρ p), hallowed⟩
  have he : field 0 hB0 z = field 0 hB0 x₀ := by
    rw [extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B 0 hB0 x₀ z,
      Subsingleton.elim (B.levelTransport 0 hB0 x₀ z) 1, map_one]
    rfl
  calc
    _ = d.shiftedQuotientComponent ℳ p p 0 (by simp)
        ((F).transition (Nat.zero_le k) (field k hBc x)) :=
      (d.shiftedQuotientComponent_transition ℳ p p (Nat.zero_le k) (by simp) _).symm
    _ = d.shiftedQuotientComponent ℳ p p 0 (by simp) (field 0 hB0 x₀) := by
      rw [transition_extendedCoefficientField d ℳ p ℒ H h h' D B
        (Nat.zero_le k) hB0 hBc hD hB]
    _ = d.shiftedQuotientComponent ℳ p p 0 (by simp) (field 0 hB0 z) := by rw [he]
    _ = a := by
      exact (hT x.val (mem_singleton x.val) hallowed).trans
        (Subtype.ext (DirectSum.decompose_of_mem_same ℳ a.property))

/-- The completed probe field retains the incoming coefficient in relative
degree zero at every all-order allowed endpoint. Outgoingness is required only
for extra walls of that degree visible at extended order one. -/
theorem shiftedHomogeneousComponent_completedExtendedCoefficientField_self
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hout : ∀ b, Sum.inr b ∈ D.active 1 →
      (p, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
        (D.wall (.inr b)).Outgoing)
    (x : B.Point) :
    d.shiftedHomogeneousComponent ℳ p p
        (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) = a := by
  rw [d.shiftedHomogeneousComponent_eq ℳ p p 0 (by simp),
    projection_completedExtendedCoefficientField]
  exact shiftedQuotientComponent_extendedCoefficientField_self
    d ℳ p ℒ H h h' D₀ a D B hinitial 0 ((D.consistent_iff.mp hD) 1)
    ((B.consistent_iff.mp hBc) 0) ((DirectedDiagram.equivalent_iff _ _).mp hB 0) hout _

end Mei.ModuleProbe
