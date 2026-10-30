/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Height
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Regular

/-!
# The endpoint field of probe coefficients

Outside a finite exceptional arrangement, a probe diagram has regular heights
in every open interval and its active base-wall hyperplanes miss the entire
height line. For a consistent diagram the vertical coefficient therefore
specifies a field on generic base endpoints, independent of the chosen height.
It is characterized by every regular vertical crossing, commutes with
truncation, and agrees for equivalent diagrams on their common generic locus.

The construction assembles `DirectedDiagram.exists_finite_bad_vertical_heights`,
`ModuleProbe.verticalCoefficient_eq_of_height` and the crossing coefficient API.
The field is the coefficient extracted from the module probe in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
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
local notation "F" => d.shiftedFiltration ℳ p

private theorem exists_regular_height_univ (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    ∃ y : ℝ, (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) := by
  obtain ⟨y, _, hy⟩ := exists_regular_height d ℳ p ℒ H h h' D k Q hQ isOpen_univ
    Set.univ_nonempty
  exact ⟨y, hy⟩

/-- The relative order-`k` probe coefficient at a generic endpoint, computed at
one regular height. For a consistent diagram every regular height gives this value. -/
def coefficientField (k : ℕ) (Q : V)
    (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) : (F).quotient k :=
  verticalCoefficient d ℳ p ℒ H h h' D k
    (Q, (exists_regular_height_univ d ℳ p ℒ H h h' D k Q hQ).choose • j (1, 0))
    (exists_regular_height_univ d ℳ p ℒ H h h' D k Q hQ).choose_spec

/-- At every regular height the extracted coefficient is the endpoint field.
Only consistency through the current extended order is required. -/
theorem coefficientField_eq_verticalCoefficient (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (y : ℝ) (hy : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support)) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ =
      verticalCoefficient d ℳ p ℒ H h h' D k (Q, y • j (1, 0)) hy := by
  let s := exists_regular_height_univ d ℳ p ℒ H h h' D k Q hQ
  have he := verticalCoefficient_eq_of_height d ℳ p ℒ H h h' D k hD
    (Q, y • j (1, 0)) (s.choose - y) hy
    (by simpa only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero,
      ← add_smul, add_sub_cancel] using s.choose_spec)
    (fun a ha => not_mem_base_affineSpan_of_isGeneric d ℳ p ℒ H h h' D k Q hQ y a ha)
  simpa only [coefficientField, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero,
    ← add_smul, add_sub_cancel] using he

/-- The negative exponential of the field is the upward crossing label at
every regular height, including simultaneous module-wall crossings. -/
theorem moduleBCHInclusion_neg_coefficientField [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (y : ℝ) (hy : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support)) :
    moduleBCHInclusion d ℳ p ℒ k
        (Multiplicative.ofAdd (-coefficientField d ℳ p ℒ H h h' D k Q hQ)) =
      D.combinedLabel (k + 1) (Q, y • j (1, 0)) v hy := by
  rw [coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD Q hQ y hy]
  exact moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k _ hy
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ y)

/-- A regular upward crossing uniquely characterizes the value of the field. -/
theorem coefficientField_eq_iff [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (k : ℕ) (hD : D.LevelConsistent (k + 1))
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (y : ℝ) (hy : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
    (a : (F).quotient k) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ = a ↔
      moduleBCHInclusion d ℳ p ℒ k (Multiplicative.ofAdd (-a)) =
        D.combinedLabel (k + 1) (Q, y • j (1, 0)) v hy := by
  rw [coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD Q hQ y hy]
  exact verticalCoefficient_eq_iff d ℳ p ℒ H h h' D k _ hy
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ y) a

/-- Lowering the relative cutoff preserves the endpoint field on the common
generic locus. The arrangements themselves need not be nested. -/
@[simp]
theorem transition_coefficientField {k l : ℕ} (hkl : k ≤ l)
    (hl : D.LevelConsistent (l + 1))
    (Q : V) (hQk : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQl : (coefficientArrangement d ℳ p ℒ H h h' D l).IsGeneric Q) :
    (F).transition hkl (coefficientField d ℳ p ℒ H h h' D l Q hQl) =
      coefficientField d ℳ p ℒ H h h' D k Q hQk := by
  obtain ⟨y, hy⟩ := ((finite_bad_heights d ℳ p ℒ H h h' D k Q hQk).union
    (finite_bad_heights d ℳ p ℒ H h h' D l Q hQl)).infinite_compl.nonempty
  have hyk : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
    fun hs => hy (Or.inl (Or.inl hs))
  have hyl : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (l + 1) => (D.wall a).support) :=
    fun hs => hy (Or.inr (Or.inl hs))
  rw [coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D l hl Q hQl y hyl,
    coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k
      (hl.mono (Nat.add_le_add_right hkl 1)) Q hQk y hyk,
    transition_verticalCoefficient]

/-- Equivalent consistent diagrams give the same endpoint field on their common
generic locus. Their wall presentations and choices of regular height may differ. -/
theorem coefficientField_eq_of_levelEquivalent {κ : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) κ) (k : ℕ) (hDD' : D.LevelEquivalent D' (k + 1))
    (hD : D.LevelConsistent (k + 1))
    (Q : V) (hQ : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : (coefficientArrangement d ℳ p ℒ H h h' D' k).IsGeneric Q) :
    coefficientField d ℳ p ℒ H h h' D k Q hQ =
      coefficientField d ℳ p ℒ H h h' D' k Q hQ' := by
  obtain ⟨y, hy⟩ := ((finite_bad_heights d ℳ p ℒ H h h' D k Q hQ).union
    (finite_bad_heights d ℳ p ℒ H h h' D' k Q hQ')).infinite_compl.nonempty
  have hyD : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
    fun hs => hy (Or.inl (Or.inl hs))
  have hyD' : (Q, y • j (1, 0)) ∉
      singularSupport (fun a : D'.active (k + 1) => (D'.wall a).support) :=
    fun hs => hy (Or.inr (Or.inl hs))
  rw [coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD Q hQ y hyD,
    coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D' k (hDD'.consistent hD) Q hQ' y hyD']
  exact verticalCoefficient_eq_of_levelEquivalent d ℳ p ℒ H h h' D D' hDD' _ hyD hyD'
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k Q hQ y)
    (vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D' k Q hQ' y)

end Mei.ModuleProbe
