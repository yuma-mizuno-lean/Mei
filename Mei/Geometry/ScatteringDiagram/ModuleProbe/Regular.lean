/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Crossing
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Vertical

/-!
# Generic endpoints admit probe coefficients

At each relative cutoff there is a finite exceptional arrangement of base
endpoints above which regular probe heights can be chosen in every nonempty
open interval. At these heights arbitrarily short upward crossings compute the
negative exponential of the extracted coefficient. This applies to every probe
diagram, in particular to outgoing completions of the initial cylinders and
probe wall; consistency and purity of birth logarithms are unnecessary.

We combine `DirectedDiagram.exists_finite_bad_vertical_heights` with
`ModuleProbe.eventually_exists_levelPathProduct_eq_moduleBCHInclusion_neg_verticalCoefficient`.
The construction follows Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
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

local notation "v" => (0, j (0, 1))

/-- Generic base endpoints admit a regular probe height in every nonempty open
interval. All sufficiently short upward crossings at that height compute the
negative exponential of the same relative order-`k` coefficient. -/
theorem exists_verticalCoefficient_arrangement (k : ℕ) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      ∀ U : Set ℝ, IsOpen U → U.Nonempty →
        ∃ y ∈ U, ∃ (hθ : (Q, y • j (1, 0)) ∉
            singularSupport (fun a : D.active (k + 1) => (D.wall a).support)),
          (∀ a : D.active (k + 1), (Q, y • j (1, 0)) ∈ (D.wall a).support →
            (h.prod h').realCharacter (D.wall a).normal v ≠ 0) ∧
          ∀ᶠ t : ℝ in 𝓝[>] 0,
            ∃ (x z : WallComplement (fun a : D.active (k + 1) => (D.wall a).support))
              (e : x ⟶ z),
              x.val = (Q, y • j (1, 0)) - t • v ∧
              z.val = (Q, y • j (1, 0)) + t • v ∧
              D.levelPathProduct (k + 1) e.toPath = moduleBCHInclusion d ℳ p ℒ k
                (Multiplicative.ofAdd
                  (-verticalCoefficient d ℳ p ℒ H h h' D k (Q, y • j (1, 0)) hθ)) := by
  obtain ⟨A, hA⟩ := D.exists_finite_bad_vertical_heights h h' (k + 1)
  refine ⟨A, fun Q hQ U hU hUne => ?_⟩
  obtain ⟨y, hyU, hy⟩ := (dense_univ.sdiff_finite (hA Q hQ)).inter_open_nonempty U hU hUne
  have hygood := hy.2
  have hθ : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
    fun hs => hygood (Or.inl hs)
  have hv : ∀ a : D.active (k + 1), (Q, y • j (1, 0)) ∈ (D.wall a).support →
      (h.prod h').realCharacter (D.wall a).normal v ≠ 0 :=
    fun a ha hz => hygood (Or.inr ⟨a, ha, hz⟩)
  exact ⟨y, hyU, hθ, hv,
    eventually_exists_levelPathProduct_eq_moduleBCHInclusion_neg_verticalCoefficient
      d ℳ p ℒ H h h' D k _ hθ hv⟩

end Mei.ModuleProbe
