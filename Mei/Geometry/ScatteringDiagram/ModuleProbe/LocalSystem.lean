/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Extension
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Realization.Basic
public import Mei.Geometry.ScatteringDiagram.Coefficient.LocalSystem
public import Mei.Topology.Sheaves.DenseBasisTransport.Extension

/-!
# Probe coefficients as sections of the coefficient local system

At a finite cutoff the probe coefficient field, initially defined only at generic
endpoints, extends uniquely to the existing coefficient local system of an
adapted finite base diagram. The chart equations are the base path-transport
theorem, and density supplies the missing coefficient points. This construction
includes regular points on walls through the ambient sheaf condition.

The construction combines
`coefficientField_eq_truncatedBCHAction_levelPathProduct`,
`DirectedDiagram.levelPathProduct_eq_adaptedDiagram`, and
`DenseBasisTransport.existsUnique_section_of_dense`.

The domain is the regular locus of the chosen adapted complex, which may omit
artificial strata introduced by the subdivision. No identification with a
broken-line sum or extension to the maximal original regular locus is asserted.
-/

public noncomputable section

open Set TopologicalSpace Opposite Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
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
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ)

local notation "F" => d.shiftedFiltration ℳ p

/-- The existing finite BCH representation, expressed as the action needed by
the coefficient local system. -/
abbrev coefficientMulAction (k : ℕ) :
    MulAction (d.truncatedGroup ℒ k) ((F).quotient k) :=
  MulAction.compHom _ ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k)

attribute [local instance] coefficientMulAction

/-- Generic probe endpoints among the coefficient points of the adapted base
complex. Genericity is required only for the initial coefficient field. -/
abbrev coefficientGenericPoints (k : ℕ) :=
  {x : (B.adaptedComplex k).coefficientPoints //
    (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val.val}

/-- The generic probe endpoints remain dense in the full adapted regular locus,
including regular wall points. -/
theorem denseRange_coefficientGenericPoints (k : ℕ) :
    DenseRange (fun a : coefficientGenericPoints d ℳ p ℒ H h h' D B k => a.val.val) := by
  let := h.finiteDimensional
  let C := B.adaptedComplex k
  let A := coefficientArrangement d ℳ p ℒ H h h' D k
  have hdA : Dense {x : C.regularSpace | A.IsGeneric x.val} :=
    A.dense_isGeneric.preimage C.isOpen_regularLocus.isOpenMap_subtype_val
  have hoA : IsOpen {x : C.regularSpace | A.IsGeneric x.val} :=
    A.isOpen_isGeneric.preimage continuous_subtype_val
  have hd := C.dense_coefficientPoints.inter_of_isOpen_right hdA hoA
  change Dense (Set.range _)
  apply hd.mono
  rintro x ⟨hx, hA⟩
  exact ⟨⟨⟨x, hx⟩, hA⟩, rfl⟩

variable (k : ℕ) (ν : (B.adaptedComplex k).walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ Q, (ν Q).ker = (affineSpan ℝ (Q : Set V)).direction)
  (hD : D.LevelConsistent (k + 1))
  (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
    (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
    (cylinderDiagram d ℳ p ℒ H h h' B) k)

include hD hB

/-- On every adapted transport chart, generic probe coefficients satisfy the
original finite coefficient transport, including crossings of base walls. -/
theorem coefficientField_parallel (U : Opens (B.adaptedComplex k).regularSpace)
    (hU : U ∈ (B.adaptedComplex k).coefficientCharts)
    (a b : coefficientGenericPoints d ℳ p ℒ H h h' D B k)
    (ha : a.val.val ∈ U) (hb : b.val.val ∈ U) :
    ((B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)).transport U
      (by simpa using hU)
      a.val b.val ha hb
      (coefficientField d ℳ p ℒ H h h' D k a.val.val.val a.property) =
        coefficientField d ℳ p ℒ H h h' D k b.val.val.val b.property := by
  let γ := (B.adaptedComplex k).coefficientSegment U hU a.val b.val ha hb
  have hp := coefficientField_eq_truncatedBCHAction_levelPathProduct
    d ℳ p ℒ H h h' D B k hD hB
    ((B.adaptedPathPrefunctor k).mapPath γ.toPath)
    (by simpa only [B.adaptedPathPrefunctor_obj_val] using a.property)
    (by simpa only [B.adaptedPathPrefunctor_obj_val] using b.property)
  rw [B.levelPathProduct_eq_adaptedDiagram ν hν γ.toPath] at hp
  simp only [B.adaptedPathPrefunctor_obj_val] at hp
  rw [FiniteWallDiagram.coefficientTransport_transport,
    FiniteWallDiagram.coefficientPathTransport_apply]
  exact hp.symm

/-- The unique ambient local-system section with the generic probe coefficients.
It is constructed in the existing coefficient sheaf of the adapted base diagram. -/
theorem existsUnique_coefficientLocalSection :
    ∃! s : ((B.adaptedDiagram k ν hν).coefficientLocalSystem ((F).quotient k)).presheaf.obj
      (op (⊤ : Opens (B.adaptedComplex k).regularSpace)),
      ∀ a : coefficientGenericPoints d ℳ p ℒ H h h' D B k,
        ((B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)).value s a.val
          (by trivial) = coefficientField d ℳ p ℒ H h h' D k a.val.val.val a.property := by
  apply DenseBasisTransport.existsUnique_section_of_dense _
    (fun a : coefficientGenericPoints d ℳ p ℒ H h h' D B k => a.val)
    (denseRange_coefficientGenericPoints d ℳ p ℒ H h h' D B k)
    (fun a => coefficientField d ℳ p ℒ H h h' D k a.val.val.val a.property)
  intro U hU a b ha hb
  exact coefficientField_parallel d ℳ p ℒ H h h' D B k ν hν hD hB U
    (by simpa using hU) a b ha hb

/-- Probe coefficients extend from generic endpoints to an actual section over
the entire regular locus of the chosen adapted base complex. -/
def coefficientLocalSection :
    ((B.adaptedDiagram k ν hν).coefficientLocalSystem ((F).quotient k)).presheaf.obj
      (op (⊤ : Opens (B.adaptedComplex k).regularSpace)) :=
  (existsUnique_coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB).choose

/-- The constructed section recovers the original generic coefficient field. -/
@[simp]
theorem value_coefficientLocalSection
    (x : (B.adaptedComplex k).coefficientPoints)
    (hx : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val.val) :
    ((B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)).value
      (coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB) x (by trivial) =
        coefficientField d ℳ p ℒ H h h' D k x.val.val hx :=
  (existsUnique_coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB).choose_spec.1 ⟨x, hx⟩

/-- At every adapted coefficient point, the ambient section equals the endpoint
extension by consistent base transport. No genericity is required at this point. -/
theorem value_coefficientLocalSection_eq_extendedCoefficientField
    (hBc : B.LevelConsistent k) (x : (B.adaptedComplex k).coefficientPoints) :
    ((B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)).value
      (coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB) x (by trivial) =
        extendedCoefficientField d ℳ p ℒ H h h' D B k hBc
          ((B.adaptedPathPrefunctor k).obj ⟨x.val.val, x.property⟩) := by
  let T := (B.adaptedDiagram k ν hν).coefficientTransport ((F).quotient k)
  let g (y : (B.adaptedComplex k).coefficientPoints) :=
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc
      ((B.adaptedPathPrefunctor k).obj ⟨y.val.val, y.property⟩)
  have hg : T.prelocal.pred
      (fun (y : (⊤ : Opens (B.adaptedComplex k).regularSpace)) hy => g ⟨y.val, hy⟩) := by
    rw [DenseBasisTransport.prelocal_pred_iff]
    intro U hU _ a b ha hb
    have hU' : U ∈ (B.adaptedComplex k).coefficientCharts := by simpa [T] using hU
    let γ := (B.adaptedComplex k).coefficientSegment U hU' a b ha hb
    have he := extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k hBc hD hB
      ((B.adaptedPathPrefunctor k).obj ⟨a.val.val, a.property⟩)
      ((B.adaptedPathPrefunctor k).obj ⟨b.val.val, b.property⟩)
    rw [B.levelTransport_eq_levelPathProduct hBc
      ((B.adaptedPathPrefunctor k).mapPath γ.toPath),
      B.levelPathProduct_eq_adaptedDiagram ν hν γ.toPath] at he
    change T.transport U hU a b ha hb (g a) = g b
    dsimp only [T]
    rw [FiniteWallDiagram.coefficientTransport_transport,
      FiniteWallDiagram.coefficientPathTransport_apply]
    exact he.symm
  let t := T.sectionOfLocallyParallel (fun y hy => g ⟨y.val, hy⟩)
    (TopCat.PrelocalPredicate.sheafifyOf hg)
  have ht : t = coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB := by
    apply T.section_ext_of_dense
      (fun a : coefficientGenericPoints d ℳ p ℒ H h h' D B k => a.val)
      (denseRange_coefficientGenericPoints d ℳ p ℒ H h h' D B k)
    intro a ha
    dsimp only [t]
    rw [DenseBasisTransport.value_sectionOfLocallyParallel]
    rw [value_coefficientLocalSection d ℳ p ℒ H h h' D B k ν hν hD hB a.val a.property]
    simpa only [g, B.adaptedPathPrefunctor_obj_val] using
      extendedCoefficientField_eq_coefficientField d ℳ p ℒ H h h' D B k hBc hD hB
        ((B.adaptedPathPrefunctor k).obj ⟨a.val.val.val, a.val.property⟩)
        (by simpa only [B.adaptedPathPrefunctor_obj_val] using a.property)
  rw [← ht]
  exact T.value_sectionOfLocallyParallel _ _ x (by trivial)

end Mei.ModuleProbe
