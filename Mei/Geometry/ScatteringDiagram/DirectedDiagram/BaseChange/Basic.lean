/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.DirectedWall.BaseChange

/-!
# Scalar extension of directed diagrams

Let `D` be a directed diagram for wall spaces `H` of a positively graded Lie algebra `g` over a
commutative `ℚ`-algebra `R`, and let `S` be a commutative `R`-algebra that is also a
`ℚ`-algebra, in the universe of `g`. Extending the scalars of every wall along `x ↦ 1 ⊗ x`
(`DirectedWall.baseChange`) gives a diagram `D.baseChange S` for the extended wall spaces
`H.baseChange S` on `S ⊗[R] g`, with the same index, supports, normals and supported rays
(`DirectedDiagram.baseChange`). It is the coefficient change
`DirectedDiagram.mapRestrictScalars` over the common base ring `R`, so scalar extension preserves
consistency (`DirectedDiagram.Consistent.baseChange`), equivalence
(`DirectedDiagram.Equivalent.baseChange`) and outgoing completions
(`DirectedDiagram.IsOutgoingCompletion.baseChange`). It carries every representative of the
scattering class of a full-hyperplane input to a representative of the scattering class of the
extended input (`DirectedDiagram.toClass_baseChange_eq_scat`); in particular the scattering class
of the extended input is the class of the extended outgoing completion
(`DirectedDiagram.scat_baseChange_eq_toClass`). No flatness of `S` is assumed; walls whose labels
vanish after scalar extension remain in the diagram with trivial label.

At finite order the labels of `D.baseChange S` are computed in `S ⊗[R] g≤k` by
`DirectedWall.bchGroupMap_projection_baseChange_label`.

This is the change of coefficient ring of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, Example 2.1(i) (arXiv:1503.06183v5), for scalar extension.
-/

public section

noncomputable section

open TensorProduct

namespace Mei.DirectedDiagram

universe u v

variable {Γ Λ R V ι : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ R L] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}
  (S : Type u) [CommRing S] [Algebra R S] [Algebra ℚ S]
  (D : DirectedDiagram (d := d) h H ι)

/-- Extend the scalars of every wall of a directed diagram along `x ↦ 1 ⊗ x`, retaining every
index, support, normal and supported ray. -/
def baseChange : DirectedDiagram (d := d) h (H.baseChange S) ι :=
  D.mapRestrictScalars (GradedLieHom.includeRight S ℒ)
    (H.includeRight_mem_restrictScalars_baseChange_wall S)

/-- Scalar extension is the coefficient change along `x ↦ 1 ⊗ x`. -/
theorem baseChange_def :
    D.baseChange S = D.mapRestrictScalars (GradedLieHom.includeRight S ℒ)
      (H.includeRight_mem_restrictScalars_baseChange_wall S) := (rfl)

/-- Extending the scalars of a diagram extends them on each wall. -/
@[simp]
theorem baseChange_wall (j : ι) : (D.baseChange S).wall j = (D.wall j).baseChange S := by
  rw [baseChange_def, mapRestrictScalars_wall, DirectedWall.baseChange_def]

variable {D}

/-- Scalar extension preserves consistency. -/
theorem Consistent.baseChange (hD : D.Consistent) : (D.baseChange S).Consistent :=
  hD.mapRestrictScalars _ _

/-- Scalar extension preserves equivalence. -/
theorem Equivalent.baseChange {κ : Type*} {E : DirectedDiagram (d := d) h H κ}
    (hDE : D.Equivalent E) : (D.baseChange S).Equivalent (E.baseChange S) :=
  hDE.mapRestrictScalars _ _

/-- Scalar extension sends an outgoing completion to an outgoing completion of the extended
input, even when some labels vanish. -/
theorem IsOutgoingCompletion.baseChange {ι₀ ι' : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).baseChange S) (E.baseChange S) := by
  simpa only [DirectedWall.baseChange_def, baseChange_def] using hE.mapRestrictScalars _ _

variable [Module.Free ℤ Γ]

/-- Scalar extension carries every representative of the scattering class of a full-hyperplane
input to a representative of the scattering class of the extended input. -/
theorem toClass_baseChange_eq_scat {ι : Type v} (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    {κ : Type v} {E : DirectedDiagram (d := d) h H κ} (hE : E.toClass = D.Scat hfull) :
    (E.baseChange S).toClass = (D.baseChange S).Scat (by
      simpa only [baseChange_wall, DirectedWall.baseChange_support,
        DirectedWall.baseChange_normal] using hfull) :=
  toClass_mapRestrictScalars_eq_scat _ _ D hfull hE

/-- The scattering class of the scalar extension of a full-hyperplane input is the class of the
scalar extension of any outgoing completion of the input. -/
theorem scat_baseChange_eq_toClass {ι : Type v} (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    {η : Type v} {E : DirectedDiagram (d := d) h H (ι ⊕ η)}
    (hE : IsOutgoingCompletion D.wall E) :
    (D.baseChange S).Scat (by
      simpa only [baseChange_wall, DirectedWall.baseChange_support,
        DirectedWall.baseChange_normal] using hfull) = (E.baseChange S).toClass :=
  (toClass_baseChange_eq_scat S D hfull (scat_eq_toClass D hfull hE).symm).symm

end Mei.DirectedDiagram
