/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Crossing

/-!
# Transport of probe coefficients by arbitrary labels

Conjugating a module label by any probe label acts on its coefficient by the
BCH action of the base projection. Thus module contributions in a transporting
label do not alter coefficient transport. The formulas hold at finite order
and in the completion, without a faithful coefficient action.

For vertical regular germs, the coefficient transport equation is equivalent
to conjugacy of their upward crossing labels. The minus sign in an upward
crossing cancels by linearity. This is the algebraic passage from probe
rectangles to transport of their coefficients. For a consistent diagram, two
admissible routes with equal side products give the coefficient equation; the
existence of such routes is a separate geometric condition.

We use `MonoidHom.conj_eq_of_apply_eq`, the kernel descriptions in
`ModuleProbe.Projection`, and the charge-zero conjugation formulas in
`ModuleProbe.Conjugation` and `ModuleProbe.Completion`.
The probe interpretation follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]

local notation "π" => baseQuotientProjection d ℳ p ℒ

variable {Λ V E ι : Type*} [AddCommGroup Λ] {ρ : Γ →+ Λ}
  (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)

local notation "v" => (0, j (0, 1))

/-- Transport of vertical coefficients is equivalent to conjugacy of the
upward crossing labels. The transporting label may have any module component;
only its base projection enters the coefficient equation. -/
theorem verticalCoefficient_eq_action_iff (k : ℕ) (θ θ' : V × E)
    (hθ : θ ∉ singularSupport
      (fun a : D.active (k + 1) => (D.wall a).support))
    (hθ' : θ' ∉ singularSupport
      (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    (hv' : ∀ a : D.active (k + 1), θ' ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    (g : BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1))) :
    verticalCoefficient d ℳ p ℒ H h h' D k θ' hθ' =
        (d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
          ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap ((π (k + 1)).bchGroupMap g))
          (verticalCoefficient d ℳ p ℒ H h h' D k θ hθ) ↔
      D.combinedLabel (k + 1) θ' v hθ' =
        g * D.combinedLabel (k + 1) θ v hθ * g⁻¹ := by
  rw [← moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k θ hθ hv,
    ← moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k θ' hθ' hv',
    conj_moduleBCHInclusion]
  simp only [toAdd_ofAdd, map_neg, (moduleBCHInclusion_injective d ℳ p ℒ k).eq_iff,
    Multiplicative.ofAdd.injective.eq_iff, neg_inj]

/-- In a consistent diagram, paths realizing two upward crossings and having
matching side transports give the base-action transport equation on coefficients.
The equality of side products is an explicit hypothesis; this theorem does not
assert the existence of a geometric rectangle with that property. -/
theorem verticalCoefficient_eq_action_of_paths (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (θ θ' : V × E)
    (hθ : θ ∉ singularSupport
      (fun a : D.active (k + 1) => (D.wall a).support))
    (hθ' : θ' ∉ singularSupport
      (fun a : D.active (k + 1) => (D.wall a).support))
    (hv : ∀ a : D.active (k + 1), θ ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    (hv' : ∀ a : D.active (k + 1), θ' ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    {x₀ x₁ y₀ y₁ : WallComplement
      (fun a : D.active (k + 1) => (D.wall a).support)}
    (e : AdmissiblePLPath x₀ x₁) (f : AdmissiblePLPath y₀ y₁)
    (r₀ : AdmissiblePLPath x₀ y₀) (r₁ : AdmissiblePLPath x₁ y₁)
    (he : D.levelPathProduct (k + 1) e = D.combinedLabel (k + 1) θ v hθ)
    (hf : D.levelPathProduct (k + 1) f = D.combinedLabel (k + 1) θ' v hθ')
    (hr : D.levelPathProduct (k + 1) r₁ = D.levelPathProduct (k + 1) r₀) :
    verticalCoefficient d ℳ p ℒ H h h' D k θ' hθ' =
      (d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        ((d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
          ((π (k + 1)).bchGroupMap (D.levelPathProduct (k + 1) r₀)))
        (verticalCoefficient d ℳ p ℒ H h h' D k θ hθ) := by
  apply (verticalCoefficient_eq_action_iff d ℳ p ℒ H h h' D k θ θ' hθ hθ' hv hv'
    (D.levelPathProduct (k + 1) r₀)).mpr
  have hc := (D.levelConsistent_def (k + 1)).mp hD (e.comp r₁) (r₀.comp f)
  rw [D.levelPathProduct_comp, D.levelPathProduct_comp, he, hf, hr] at hc
  exact (eq_mul_inv_iff_mul_eq
    (G := BCHGroup ((positiveDegrees d p).truncatedLie (grading d ℳ p ℒ) (k + 1)))).mpr
    hc.symm

end Mei.ModuleProbe
