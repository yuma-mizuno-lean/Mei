/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.PathTransport

/-!
# Completed endpoint fields of module probes

At an endpoint generic for every finite-order probe arrangement, the extracted
coefficients form an element of the existing completed shifted module. Its
projections characterize it, and equivalent consistent probe diagrams give the
same element on their common generic locus.

The completed field obeys transport by the completed base path product. For
outgoing completions of a base input and its probe input, this gives transport
between all-order allowed endpoints, independently of a choice of path. No
single auxiliary height, stabilization of the wall supports, or separatedness
of the original coefficient module is required. Identification with sums of
broken lines is a separate result.

We assemble `ModuleProbe.transition_coefficientField` using
`ModuleFiltration.completionSubmodule`, and use
`ModuleProbe.coefficientField_eq_truncatedBCHAction_levelPathProduct` and
`ModuleFiltration.projection_completedBCHAction` for transport. The probe
interpretation follows Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

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

local notation "F" => d.shiftedFiltration ℳ p

/-- The compatible finite probe coefficients at an endpoint generic at every
cutoff, viewed in the completed shifted module. Each cutoff may use a different
regular height. -/
def completedCoefficientField (hD : D.Consistent) (Q : V)
    (hQ : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) :
    (F).completion :=
  ⟨fun k => coefficientField d ℳ p ℒ H h h' D k.unop Q (hQ k.unop),
    ((F).mem_completionSubmodule_iff _).mpr fun k l hkl =>
      transition_coefficientField d ℳ p ℒ H h h' D hkl
        ((D.consistent_iff.mp hD) (l + 1)) Q (hQ k) (hQ l)⟩

/-- Projecting the completed endpoint field recovers the actual finite-order
coefficient extracted from vertical wall crossings. -/
@[simp]
theorem projection_completedCoefficientField (hD : D.Consistent) (Q : V)
    (hQ : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q) (k : ℕ) :
    (F).projection k (completedCoefficientField d ℳ p ℒ H h h' D hD Q hQ) =
      coefficientField d ℳ p ℒ H h h' D k Q (hQ k) := by
  rw [completedCoefficientField, ModuleFiltration.projection_mk]

/-- The completed endpoint field is uniquely characterized by all its finite
crossing coefficients. -/
theorem completedCoefficientField_eq_iff (hD : D.Consistent) (Q : V)
    (hQ : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (a : (F).completion) :
    completedCoefficientField d ℳ p ℒ H h h' D hD Q hQ = a ↔
      ∀ k, coefficientField d ℳ p ℒ H h h' D k Q (hQ k) = (F).projection k a := by
  constructor
  · rintro rfl k
    exact (projection_completedCoefficientField d ℳ p ℒ H h h' D hD Q hQ k).symm
  · intro ha
    exact (F).completion_ext fun k =>
      (projection_completedCoefficientField d ℳ p ℒ H h h' D hD Q hQ k).trans (ha k)

/-- Equivalent consistent probe diagrams define the same completed coefficient
on their common all-order generic locus. -/
theorem completedCoefficientField_eq_of_equivalent {κ : Type*}
    (D' : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) κ) (hDD' : D.Equivalent D') (hD : D.Consistent)
    (Q : V) (hQ : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric Q)
    (hQ' : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D' k).IsGeneric Q) :
    completedCoefficientField d ℳ p ℒ H h h' D hD Q hQ =
      completedCoefficientField d ℳ p ℒ H h h' D' (hDD'.consistent hD) Q hQ' := by
  apply (F).completion_ext
  intro k
  simp only [projection_completedCoefficientField]
  exact coefficientField_eq_of_levelEquivalent d ℳ p ℒ H h h' D D' k
    ((DirectedDiagram.equivalent_iff _ _).mp hDD' (k + 1))
    ((D.consistent_iff.mp hD) (k + 1)) Q (hQ k) (hQ' k)

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Completed probe coefficients are transported by the completed base product
along every common all-order admissible path, provided the charge-zero diagram
is equivalent to the base cylinder. No separate consistency hypothesis on
the base is needed. -/
theorem completedCoefficientField_eq_completedBCHAction_pathProduct {κ : Type*}
    (B : DirectedDiagram (d := d) h H κ) (hD : D.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
        (cylinderDiagram d ℳ p ℒ H h h' B))
    {x y : B.Point} (γ : Quiver.Path x y)
    (hx : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val)
    (hy : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric y.val) :
    completedCoefficientField d ℳ p ℒ H h h' D hD y.val hy =
      (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ (B.pathProduct γ)
        (completedCoefficientField d ℳ p ℒ H h h' D hD x.val hx) := by
  apply (F).completion_ext
  intro k
  rw [(d.shiftedLieFiltration ℒ ℳ p).projection_completedBCHAction,
    projection_completedCoefficientField, projection_completedCoefficientField,
    B.projection_pathProduct]
  exact coefficientField_eq_truncatedBCHAction_levelPathProduct d ℳ p ℒ H h h' D B k
    ((D.consistent_iff.mp hD) (k + 1)) ((DirectedDiagram.equivalent_iff _ _).mp hB k)
    ((CommonWallComplement.projectionPrefunctor k).mapPath γ) (hx k) (hy k)

/-- For outgoing completions of a base input and its probe input, the completed
endpoint field is transported by the base completion's endpoint transport.
All geometric paths and auxiliary crossing heights have been eliminated from
the statement. -/
theorem completedCoefficientField_eq_completedBCHAction_transport_of_isOutgoingCompletion
    {ι₀ κ κ' : Type*} (D₀ : DirectedDiagram (d := d) h H ι₀)
    (C : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)) (a : ℳ p)
    (P : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((ι₀ ⊕ Unit) ⊕ κ'))
    (hC : DirectedDiagram.IsOutgoingCompletion D₀.wall C)
    (hP : DirectedDiagram.IsOutgoingCompletion (initialDiagram d ℳ p ℒ H h h' D₀ a).wall P)
    (x y : C.Point)
    (hx : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' P k).IsGeneric x.val)
    (hy : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' P k).IsGeneric y.val) :
    completedCoefficientField d ℳ p ℒ H h h' P hP.consistent y.val hy =
      (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ (C.transport hC.consistent x y)
        (completedCoefficientField d ℳ p ℒ H h h' P hP.consistent x.val hx) := by
  obtain ⟨γ⟩ := C.exists_path x y
  rw [C.transport_eq_pathProduct hC.consistent γ]
  exact completedCoefficientField_eq_completedBCHAction_pathProduct d ℳ p ℒ H h h' P C
    hP.consistent (map_chargeZeroGradedLieHom_equivalent_cylinderDiagram_of_isOutgoingCompletion
      d ℳ p ℒ H h h' D₀ C a P hC hP) γ hx hy

end Mei.ModuleProbe
