/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Asymptotic.Extension
public import Mei.Geometry.Convex.Polyhedron.Path.Ray

/-!
# Backward segments with the incoming probe coefficient

One finite exceptional arrangement of endpoints works for every coefficient
degree retained at a fixed order. From a generic endpoint, all sufficiently
distant points in each degree's positive spatial direction are joined back to
the endpoint by an actual admissible straight segment. At its starting point,
the probe component already has its incoming value. Thus finite segment
transport can start at the incoming value in the backward-ray recursion.

Zero spatial directions give constant segments and the same incoming component
identity. Distinct coefficient degrees with the same direction remain distinct.
No genericity for the auxiliary probe arrangement is required at either end.

We combine `Convex.exists_ray_admissibilityArrangement` with
`ModuleProbe.eventually_shiftedQuotientComponent_extendedCoefficientField_eq`.
The interpretation follows Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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

/-- A common finite arrangement supplies admissible backward segments with the
incoming probe component at their distant starting points, for every retained
degree. Only additional active probe walls carrying that degree must be outgoing. -/
theorem exists_incomingSegmentArrangement
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ) (hD : D.LevelConsistent (k + 1)) (hBc : B.LevelConsistent k)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hout : ∀ n : d.cutoff k, ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (p + n.val, 1, 0) ∈ (D.wall (.inr b)).ray.rayDegrees →
        (D.wall (.inr b)).Outgoing) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∃ y : WallComplement (fun c : B.active k => (B.wall c).support),
        y.val = Q ∧ ∀ n : d.cutoff k, ∀ᶠ T : ℝ in atTop,
          ∃ (x : WallComplement (fun c : B.active k => (B.wall c).support)) (_e : x ⟶ y),
            x.val = Q + T • i (ρ (p + n.val)) ∧
              d.shiftedQuotientComponent ℳ p (p + n.val) k
                (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
                (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x) =
                  DirectSum.decompose ℳ (a : M) (p + n.val) := by
  classical
  let := h.finiteDimensional
  let vectors := (d.finite_cutoff k).toFinset.image (fun n => i (ρ (p + n)))
  obtain ⟨A, hA⟩ := exists_ray_admissibilityArrangement
    (fun c : B.active k => (B.wall c).support)
    (fun c => (B.wall c).isConvexPolyhedron)
    (fun c => (B.wall c).finrank_direction_add_one) vectors
  refine ⟨A, fun Q hQ => ?_⟩
  obtain ⟨y, hy, hsegment⟩ := hA Q hQ
  refine ⟨y, hy, fun n => ?_⟩
  have hn : i (ρ (p + n.val)) ∈ vectors :=
    Finset.mem_image.mpr ⟨n.val, (d.finite_cutoff k).mem_toFinset.mpr n.property, rfl⟩
  have hk : d.degree ((p + n.val) - p) ≤ k := by
    simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2
  filter_upwards [hsegment _ hn,
    eventually_shiftedQuotientComponent_extendedCoefficientField_eq
      d ℳ p ℒ H h h' D₀ a D B hinitial k hD hBc hB (p + n.val) hk
      (hout n) (isCompact_singleton (x := Q))] with T hT hvalue
  obtain ⟨x, hx, he⟩ := hT
  refine ⟨x, ⟨he⟩, hx, ?_⟩
  have heq : (⟨Q + T • i (ρ (p + n.val)), by rw [← hx]; exact x.notMem⟩ :
      WallComplement (fun c : B.active k => (B.wall c).support)) = x :=
    WallComplement.ext hx.symm
  simpa only [heq] using hvalue Q (mem_singleton Q)
    (by rw [← hx]; exact x.notMem)

end Mei.ModuleProbe
