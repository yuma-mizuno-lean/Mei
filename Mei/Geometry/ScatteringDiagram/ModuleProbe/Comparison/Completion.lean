/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Comparison

/-!
# All-order weighted ray sums and probe transport

For a fixed incoming homogeneous coefficient, the actual finite weighted ray
sums form a compatible family on a dense Gδ set of endpoints. The active-wall
inventory varies with the cutoff. Compatibility is proved using the independent
finite probe comparison and probe cutoff coherence, rather than assumed from
compatibility of a fixed geometric inventory.

The unique inverse-limit value is constructed from those actual sums. Its equality with
the completed probe field gives endpoint transport for the completed ray values.
The exceptional arrangements may depend on the incoming coefficient, and the
common locus need not be open. No boundary admissibility or equality on the full
broken-line generic locus is claimed.

The construction uses `exists_extendedCoefficientField_eq_cutoffWallEventEvaluation`,
`transition_extendedCoefficientField`, and the existing countable generic-locus
and module-completion APIs. The geometric interpretation follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

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
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')


local notation "F" => d.shiftedFiltration ℳ p
local notation "action" => d.shiftedLieFiltration ℒ ℳ p

variable (b : (k : ℕ) → (d.shiftedQuotientGrading ℳ p k).piece 0)

local notation "evaluation" =>
  (fun (k : ℕ) (Q : V) =>
    cutoffWallEventEvaluation d ℳ p ℒ H h B k k (Nat.le_refl k) (b k) univ Q)

/-- Assemble completed actual ray values from finite comparison on any family
of allowed endpoints. Geometric inventories vary with the cutoff; their
compatibility follows from the probe transition law. No genericity, initial
wall, or outgoing-wall assumptions are needed beyond the supplied equality.
The probe diagram may use any indexing type, including an empty one. -/
theorem exists_completedWallEventEvaluation_of_eq
    {η : Type*} (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) η)
    (hBc : B.Consistent) (hD : D.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    {X : Type*} (point : X → B.Point)
    (hvalue : ∀ Q k, extendedCoefficientField d ℳ p ℒ H h h' D B k
      ((B.consistent_iff.mp hBc) k) (CommonWallComplement.projection k (point Q)) =
        evaluation k (point Q).val) :
    ∃ Θ : X → (F).completion,
      (∀ Q k l (hkl : k ≤ l), (F).transition hkl
        (evaluation l (point Q).val) = evaluation k (point Q).val) ∧
      (∀ Q k, (F).projection k (Θ Q) = evaluation k (point Q).val) ∧
      (∀ Q Ψ, (∀ k, (F).projection k Ψ = evaluation k (point Q).val) → Ψ = Θ Q) ∧
      (∀ Q, Θ Q = completedExtendedCoefficientField d ℳ p ℒ H h h' D B
        hD hBc hB (point Q)) ∧
      (∀ Q Q', Θ Q' = (action).completedBCHAction d ℒ
        (B.transport hBc (point Q) (point Q')) (Θ Q)) := by
  have hcompatible (Q : X) (k l : ℕ) (hkl : k ≤ l) :
      (F).transition hkl (evaluation l (point Q).val) = evaluation k (point Q).val := by
    rw [← hvalue Q l, ← hvalue Q k]
    exact transition_extendedCoefficientField d ℳ p ℒ H h h' D B hkl
      ((B.consistent_iff.mp hBc) k) ((B.consistent_iff.mp hBc) l)
      ((D.consistent_iff.mp hD) (l + 1))
      ((DirectedDiagram.equivalent_iff _ _).mp hB l)
      (CommonWallComplement.projection l (point Q))
  let Θ (Q : X) : (F).completion :=
    ⟨fun k => evaluation k.unop (point Q).val,
      ((F).mem_completionSubmodule_iff _).mpr (hcompatible Q)⟩
  have hprojection (Q : X) (k : ℕ) :
      (F).projection k (Θ Q) = evaluation k (point Q).val := by
    dsimp only [Θ]
    rw [ModuleFiltration.projection_mk]
  have hcompleted (Q : X) : Θ Q =
      completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB (point Q) := by
    apply (F).completion_ext
    intro k
    rw [hprojection, projection_completedExtendedCoefficientField]
    exact (hvalue Q k).symm
  refine ⟨Θ, hcompatible, hprojection, ?_, hcompleted, ?_⟩
  · intro Q Ψ hΨ
    exact (F).completion_ext fun k => (hΨ k).trans (hprojection Q k).symm
  · intro Q Q'
    rw [hcompleted Q, hcompleted Q']
    exact completedExtendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B hD hBc hB
      (point Q) (point Q')

/-- Actual finite ray sums at their own geometric cutoffs are compatible on a
dense Gδ common endpoint locus. Their inverse-limit values are the independently
constructed completed probe field and obey its endpoint transport. The input
family represents one fixed entire incoming coefficient; no compatibility of the
finite ray sums is assumed. -/
theorem exists_completedWallEventEvaluation
    (hinitial : ∀ c, D.wall (.inl c) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)
    (hBc : B.Consistent) (hD : D.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B))
    (hout : ∀ K, ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees →
        (D.wall (.inr c)).Outgoing)
    (hb : ∀ K, d.shiftedQuotientComponent ℳ p p K (by simp) (b K) = a) :
    ∃ A : (k : ℕ) → d.cutoff k → ExceptionalArrangement V,
      Dense {Q | ∀ k n, (A k n).IsGeneric Q} ∧
      IsGδ {Q | ∀ k n, (A k n).IsGeneric Q} ∧
      ∃ (point : {Q // ∀ k n, (A k n).IsGeneric Q} → B.Point)
        (Θ : {Q // ∀ k n, (A k n).IsGeneric Q} → (F).completion),
        (∀ Q, (point Q).val = Q.val) ∧
        (∀ Q : {Q // ∀ k n, (A k n).IsGeneric Q}, ∀ k l (hkl : k ≤ l),
          (F).transition hkl (evaluation l Q.val) = evaluation k Q.val) ∧
        (∀ Q k, (F).projection k (Θ Q) = evaluation k Q.val) ∧
        (∀ Q : {Q // ∀ k n, (A k n).IsGeneric Q}, ∀ Ψ : (F).completion,
          (∀ k, (F).projection k Ψ = evaluation k Q.val) → Ψ = Θ Q) ∧
        (∀ Q, Θ Q = completedExtendedCoefficientField d ℳ p ℒ H h h' D B
          hD hBc hB (point Q)) ∧
        (∀ Q Q', Θ Q' = (action).completedBCHAction d ℒ
          (B.transport hBc (point Q) (point Q')) (Θ Q)) := by
  classical
  let := h.finiteDimensional
  have hBk (k : ℕ) := (B.consistent_iff.mp hBc) k
  have hDk (k : ℕ) := (D.consistent_iff.mp hD) (k + 1)
  have hBk' (k : ℕ) := (DirectedDiagram.equivalent_iff _ _).mp hB k
  choose A hA using fun k =>
    exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
      d ℳ p ℒ H h h' D₀ a D B hinitial k (hBk k) (hDk k) (hBk' k) (hout k)
      (b k) (hb k)
  let Ω := {Q : V // ∀ k n, (A k n).IsGeneric Q}
  have hfinite (Q : Ω) (k : ℕ) := hA k Q.val (Q.property k)
  choose hallowed heq using hfinite
  let point (Q : Ω) : B.Point := ⟨Q.val, hallowed Q⟩
  have hvalue (Q : Ω) (k : ℕ) :
      extendedCoefficientField d ℳ p ℒ H h h' D B k (hBk k)
        (CommonWallComplement.projection k (point Q)) = evaluation k Q.val :=
    heq Q k
  obtain ⟨Θ, hcompatible, hprojection, hunique, hcompleted, htransport⟩ :=
    exists_completedWallEventEvaluation_of_eq d ℳ p ℒ H h h' B b D hBc hD hB point hvalue
  refine ⟨A, ?_, ?_, point, Θ, fun _ => rfl, hcompatible, hprojection,
    hunique, hcompleted, htransport⟩
  · simpa only [Sigma.forall] using ExceptionalArrangement.dense_iInter_isGeneric
      (fun kn : Σ k, d.cutoff k => A kn.1 kn.2)
  · simpa only [Sigma.forall] using ExceptionalArrangement.isGδ_iInter_isGeneric
      (fun kn : Σ k, d.cutoff k => A kn.1 kn.2)

end Mei.ModuleProbe
