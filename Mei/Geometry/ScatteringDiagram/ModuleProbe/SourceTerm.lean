/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion

/-!
# The probe source term, uniformly in every retained degree

The probe recursion reads its incoming datum at a far point of the backward ray:
there every retained component of the probe coefficient field equals the component of
the input in the same shifted degree. This file makes that source term available
*simultaneously for every retained degree of one cutoff*, which is the form needed to
set up the recursion as an equation on endpoint functions: one far-ray parameter must
serve all degrees, because the step operator reads several degrees at the same point.

The single-degree supplier is
`eventually_shiftedQuotientComponent_coefficientField_eq`; the uniform statement is its
finite intersection over the finite cutoff `d.cutoff k`. The zero-spatial-direction case
is `shiftedQuotientComponent_coefficientField_eq_of_spatial_eq_zero`, where the same
identity holds at every generic endpoint.

The recursion itself follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))

/-- One far-ray parameter gives the incoming datum simultaneously in every retained
degree of the cutoff `k`: the same translate `t` works for all degrees and all base
endpoints of a compact set. -/
theorem eventually_forall_shiftedQuotientComponent_coefficientField_eq
    (hinitial : ∀ b, D.wall (.inl b) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall b)
    (k : ℕ)
    (hout : ∀ (q : Γ), d.degree (q - p) ≤ (k : ℤ) →
      ∀ b, Sum.inr b ∈ D.active (k + 1) →
      (q, 1) ∈ (D.wall (.inr b)).ray.rayDegrees → (D.wall (.inr b)).Outgoing)
    {K : Set V} (hK : IsCompact K) :
    ∀ᶠ t : ℝ in atTop, ∀ n : d.cutoff k, ∀ Q ∈ K,
      ∀ hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric
          (Q + t • i (ρ (p + n.val))),
        d.shiftedQuotientComponent ℳ p (p + n.val) k
          (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
          (coefficientField d ℳ p ℒ H h h' D k (Q + t • i (ρ (p + n.val))) hQ) =
          DirectSum.decompose ℳ (a : M) (p + n.val) := by
  have hsingle : ∀ n : d.cutoff k, ∀ᶠ t : ℝ in atTop, ∀ Q ∈ K,
      ∀ hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric
          (Q + t • i (ρ (p + n.val))),
        d.shiftedQuotientComponent ℳ p (p + n.val) k
          (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
          (coefficientField d ℳ p ℒ H h h' D k (Q + t • i (ρ (p + n.val))) hQ) =
          DirectSum.decompose ℳ (a : M) (p + n.val) := by
    intro n
    have hdeg : d.degree ((p + n.val) - p) ≤ (k : ℤ) := by
      simpa only [add_sub_cancel_left] using
        (d.mem_cutoff.mp n.property).2
    exact eventually_shiftedQuotientComponent_coefficientField_eq
      d ℳ p ℒ H h h' D₀ a D hinitial k (p + n.val) hdeg (hout (p + n.val) hdeg) hK
  refine Filter.eventually_all (p := fun (n : d.cutoff k) (t : ℝ) => ∀ Q ∈ K,
    ∀ hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric
        (Q + t • i (ρ (p + n.val))),
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (by simpa only [add_sub_cancel_left] using (d.mem_cutoff.mp n.property).2)
        (coefficientField d ℳ p ℒ H h h' D k (Q + t • i (ρ (p + n.val))) hQ) =
        DirectSum.decompose ℳ (a : M) (p + n.val)) |>.mpr hsingle

end Mei.ModuleProbe
