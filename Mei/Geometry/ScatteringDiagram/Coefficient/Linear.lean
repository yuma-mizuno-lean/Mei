/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Coefficient.LocalSystem
public import Mei.Topology.Sheaves.DenseBasisTransport.Linear

/-!
# Semimodule-valued coefficient local systems

An additive wall-label action commuting with coefficient scalars makes the
coefficient local system a sheaf of semimodules over an arbitrary semiring.
Its sections, restrictions and coefficient values are the original ones.
The linear evaluation equivalence on a convex transport chart is available as
`DenseBasisTransport.evaluationLinearEquiv` for `D.coefficientTransport M`.
-/

public noncomputable section

open TopCat TopologicalSpace Opposite

namespace Mei.FiniteWallDiagram

variable {N V H : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {C : FinitePolyhedralComplex h}
  [Group H] (D : FiniteWallDiagram C H) (M : Type*) [AddCommMonoid M]
  [DistribMulAction H M]

instance coefficientTransport_isAdditive : (D.coefficientTransport M).IsAdditive where
  map_zero U hU x y hx hy := by
    have hUC : U ∈ C.coefficientCharts := by simpa only [coefficientTransport_basis] using hU
    rw [D.coefficientTransport_transport M U hUC x y hx hy, coefficientPathTransport_apply]
    exact smul_zero _
  map_add U hU x y hx hy a b := by
    have hUC : U ∈ C.coefficientCharts := by simpa only [coefficientTransport_basis] using hU
    rw [D.coefficientTransport_transport M U hUC x y hx hy]
    simp only [coefficientPathTransport_apply, smul_add]

-- Register on the concrete sheaf: inference need not reconstruct a transport
-- datum from the underlying section carrier.
instance instAddCommMonoidCoefficientSections (U : Opens C.regularSpace) :
    AddCommMonoid ((D.coefficientLocalSystem M).presheaf.obj (op U)) :=
  (D.coefficientTransport M).instAddCommMonoidSections U

variable (R : Type*) [Semiring R] [Module R M] [SMulCommClass H R M]

instance coefficientTransport_preservesSMul : (D.coefficientTransport M).PreservesSMul R where
  map_smul U hU x y hx hy a b := by
    have hUC : U ∈ C.coefficientCharts := by simpa only [coefficientTransport_basis] using hU
    rw [D.coefficientTransport_transport M U hUC x y hx hy]
    simp only [coefficientPathTransport_apply, smul_comm]

instance instModuleCoefficientSections (U : Opens C.regularSpace) :
    Module R ((D.coefficientLocalSystem M).presheaf.obj (op U)) :=
  (D.coefficientTransport M).instModuleSections R U

/-- The original coefficient local system with its semimodule structure.
Wall labels need not commute and no global consistency is assumed. -/
abbrev coefficientSemimoduleLocalSystem : C.regularSpace.Sheaf (SemimoduleCat R) :=
  (D.coefficientTransport M).semimoduleSheaf R

end Mei.FiniteWallDiagram
