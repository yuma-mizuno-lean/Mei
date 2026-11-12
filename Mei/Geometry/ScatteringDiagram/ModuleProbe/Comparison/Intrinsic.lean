/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Stable
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Stable
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison.Completion

/-!
# Intrinsic stable endpoints for completed weighted ray sums

The finite stable locus consists of allowed endpoints at which the actual total
weighted ray evaluation is locally constant. It depends on the actual sum, not
on a chosen exceptional arrangement, and includes type-domain frontier points
whenever cancellations make the sum locally constant. Each finite locus is open
and dense. Their all-order intersection is therefore a dense Gδ locus, which
need not be open. On this intrinsic locus the actual sums determine a unique
completed value and obey completed transport.

We use the finite endpoint extension from `Comparison.Stable` and the existing
completed probe field. The locus and its geometric density are supplied by
`WallEventEvaluation.Stable`, without probe or consistency hypotheses.
The incoming coefficient is fixed before taking the countable intersection.
No boundary admissibility or coefficient-uniform exceptional set is claimed.
The geometric interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

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



local notation "F" => d.shiftedFiltration ℳ p
local notation "action" => d.shiftedLieFiltration ℒ ℳ p

variable (hinitial : ∀ c, D.wall (.inl c) =
  (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)

include hinitial in
/-- Every intrinsically stable all-order endpoint has a unique completed actual
ray value on a dense locus, independently of the auxiliary arrangements, and
completed transport holds between any two of its points. The Gδ property is
provided separately by `isGδ_stableWallEventLocusAll`; compatibility across
changing geometric inventories follows from the returned projection identities. -/
theorem exists_completedWallEventEvaluation_on_stableLocus
    (hBc : B.Consistent) (hD : D.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hout : ∀ K, ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees → (D.wall (.inr c)).Outgoing)
    (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0)
    (hb : ∀ k, d.shiftedQuotientComponent ℳ p p k (by simp) (b k) = a) :
    Dense (stableWallEventLocusAll d ℳ p ℒ H h B b) ∧
    ∃ (point : stableWallEventLocusAll d ℳ p ℒ H h B b → B.Point)
      (Θ : stableWallEventLocusAll d ℳ p ℒ H h B b → (F).completion),
      (∀ Q, (point Q).val = Q.val) ∧
      (∀ Q k, (F).projection k (Θ Q) =
        cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val) ∧
      (∀ Q Ψ, (∀ k, (F).projection k Ψ =
        cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val) →
        Ψ = Θ Q) ∧
      (∀ Q, Θ Q = completedExtendedCoefficientField d ℳ p ℒ H h h' D B
        hD hBc hB (point Q)) ∧
      (∀ Q Q', Θ Q' = (action).completedBCHAction d ℒ
        (B.transport hBc (point Q) (point Q')) (Θ Q)) := by
  let := h.finiteDimensional
  have hBk (k : ℕ) := (B.consistent_iff.mp hBc) k
  have hDk (k : ℕ) := (D.consistent_iff.mp hD) (k + 1)
  have hBk' (k : ℕ) := (DirectedDiagram.equivalent_iff _ _).mp hB k
  refine ⟨dense_stableWallEventLocusAll d ℳ p ℒ H h B b, ?_⟩
  let Ω := stableWallEventLocusAll d ℳ p ℒ H h B b
  have hstable (Q : Ω) (k : ℕ) :=
    (mem_stableWallEventLocus d ℳ p ℒ H h B k (b k) Q.val).mp
      ((mem_stableWallEventLocusAll d ℳ p ℒ H h B b Q.val).mp Q.property k)
  let point (Q : Ω) : B.Point := ⟨Q.val, fun k => (hstable Q k).1⟩
  have hvalue (Q : Ω) (k : ℕ) :
      extendedCoefficientField d ℳ p ℒ H h h' D B k (hBk k)
        (CommonWallComplement.projection k (point Q)) =
      cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q.val :=
    extendedCoefficientField_eq_cutoffWallEventEvaluation_of_eventually_eq
      d ℳ p ℒ H h h' D₀ a D B hinitial k (hBk k) (hDk k) (hBk' k)
      (hout k) (b k) (hb k) (CommonWallComplement.projection k (point Q)) (hstable Q k).2
  obtain ⟨Θ, _, hprojection, hunique, hcompleted, htransport⟩ :=
    exists_completedWallEventEvaluation_of_eq d ℳ p ℒ H h h' B b D hBc hD hB point hvalue
  exact ⟨point, Θ, fun _ => rfl, hprojection, hunique, hcompleted, htransport⟩

end Mei.ModuleProbe
