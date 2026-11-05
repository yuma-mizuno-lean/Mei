/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.DevelopingMap
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exponent.Pullback

/-!
# Monodromy and trivializations of the focus-focus exponent system

Both charts of the focus-focus atlas of the punctured plane have preconnected domains
(`Mei.FocusFocus.isPreconnected_source`): the cut chart is defined off the closed upper half of
the vertical axis, a set star-convex about `(0, -1)`, and the upper chart on the upper
half-plane. Hence a trivialization of any exponent system on the punctured plane forces each
frame change to be constant on the overlap of the two chart domains
(`Mei.FocusFocus.coordChange_eq_of_trivialization`). The frame change from the cut chart to the
upper chart is the shear `upperExponent` on the left half of the overlap and the identity on its
right half, and similarly with `upperTangent` for the tangent lattice. So neither the focus-focus
exponent system nor the integral tangent lattice of the punctured plane has a trivialization
(`Mei.FocusFocus.isEmpty_exponentSystem_trivialization`,
`Mei.FocusFocus.isEmpty_tangent_trivialization`), and the punctured plane has no developing map
(`Mei.FocusFocus.isEmpty_developingMap`).

On the upper half-plane, which lies in the domain of the upper chart, the restricted exponent
system is trivialized by the frame changes to the upper chart
(`Mei.FocusFocus.upperHalfPlaneTrivialization`), although its own frame changes include the
shear, and the upper chart is a developing map (`Mei.FocusFocus.upperHalfPlaneDevelopingMap`).
Left of the vertical axis, the frame of this trivialization and the tangent frame of this
developing map in the chart at a point are the shears `upperExponent` and `upperTangent`
(`Mei.FocusFocus.upperHalfPlaneTrivialization_frame_of_neg`,
`Mei.FocusFocus.tangentFrame_upperHalfPlaneDevelopingMap_of_neg`).

The geometry is the focus-focus local model of Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2). The monodromy of its lattice local systems
around the puncture is not defined here; only the resulting absence of trivializations is
proved.
-/

public section

open Manifold TopologicalSpace

namespace Mei.FocusFocus

attribute [local instance] chartedSpace hasGroupoid

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- If an exponent system on the punctured plane has a trivialization, then each of its frame
changes takes the same value at any two points of the overlap of the two chart domains. -/
theorem coordChange_eq_of_trivialization {Γ Γ₀ : Type*} [AddCommGroup Γ] [AddCommGroup Γ₀]
    {E : Toric.ExponentSystem h regularLocus Γ} (τ : E.Trivialization Γ₀)
    (e e' : atlas (ℝ × ℝ) regularLocus) {p q : regularLocus}
    (hp : p ∈ e.1.source ∩ e'.1.source) (hq : q ∈ e.1.source ∩ e'.1.source) :
    E.coordChange e e' p = E.coordChange e e' q :=
  τ.coordChange_eq_of_isPreconnected (isPreconnected_source e) (isPreconnected_source e')
    subset_rfl subset_rfl hp hq

/-- If an exponent system on the punctured plane has a trivialization, then its frame change
from the cut chart to the upper chart at `(-1, 1)` is the same as at `(1, 1)`. -/
theorem coordChange_cutAtlas_upperAtlas_eq {Γ Γ₀ : Type*} [AddCommGroup Γ] [AddCommGroup Γ₀]
    {E : Toric.ExponentSystem h regularLocus Γ} (τ : E.Trivialization Γ₀) :
    E.coordChange cutAtlas upperAtlas ⟨(-1, 1), by simp⟩ =
      E.coordChange cutAtlas upperAtlas ⟨(1, 1), by simp⟩ :=
  coordChange_eq_of_trivialization h τ _ _ (by norm_num) (by norm_num)

/-- The focus-focus exponent system has no trivialization: its frame change from the cut chart
to the upper chart is the shear `upperExponent` at `(-1, 1)` and the identity at `(1, 1)`. -/
theorem isEmpty_exponentSystem_trivialization (Γ₀ : Type*) [AddCommGroup Γ₀] :
    IsEmpty ((exponentSystem h).Trivialization Γ₀) := by
  refine ⟨fun τ => ?_⟩
  have hτ := coordChange_cutAtlas_upperAtlas_eq h τ
  rw [exponentSystem_coordChange_of_mem h (by norm_num), exponentSystem_coordChange_of_mem h
    (by norm_num), atlasIndex_cutAtlas, atlasIndex_upperAtlas,
    latticeTransition_false_true_of_neg _ (by norm_num),
    latticeTransition_of_nonneg _ _ _ (by norm_num)] at hτ
  simpa using DFunLike.congr_fun hτ (1, 0, 0)

/-- The integral tangent lattice of the punctured plane has no trivialization: its frame change
from the cut chart to the upper chart is the shear `upperTangent` at `(-1, 1)` and the identity
at `(1, 1)`. -/
theorem isEmpty_tangent_trivialization (Γ₀ : Type*) [AddCommGroup Γ₀] :
    IsEmpty ((Toric.ExponentSystem.tangent h regularLocus).Trivialization Γ₀) := by
  refine ⟨fun τ => ?_⟩
  have hτ := coordChange_cutAtlas_upperAtlas_eq h τ
  rw [Toric.ExponentSystem.tangent_coordChange,
    tangentLatticeChange_eq_latticeTransition h (by norm_num),
    tangentLatticeChange_eq_latticeTransition h (by norm_num), atlasIndex_cutAtlas,
    atlasIndex_upperAtlas, latticeTransition_false_true_of_neg _ (by norm_num),
    latticeTransition_of_nonneg _ _ _ (by norm_num)] at hτ
  simpa using DFunLike.congr_fun hτ (1, 0)

/-- The punctured plane with its focus-focus atlas has no developing map. -/
theorem isEmpty_developingMap : IsEmpty (Toric.DevelopingMap h regularLocus) :=
  Toric.DevelopingMap.isEmpty_of_isEmpty_trivialization (isEmpty_tangent_trivialization h _)

/-- Every point of the upper half-plane lies in the domain of the upper chart. -/
theorem ofOpens_upperHalfPlane_mem_upperAtlas_source (p : upperHalfPlane) :
    AtlasMap.ofOpens (H := ℝ × ℝ) upperHalfPlane p ∈ upperAtlas.1.source := by
  rw [upperAtlas_val, AtlasMap.coe_ofOpens, mem_upperChart_source]
  exact (mem_upperHalfPlane _).mp p.2

/-- The trivialization of the focus-focus exponent system restricted to the upper half-plane by
the frame changes to the upper chart. -/
noncomputable def upperHalfPlaneTrivialization :
    ((exponentSystem h).comap (AtlasMap.ofOpens upperHalfPlane)).Trivialization
      (ℤ × ℤ × ℤ) :=
  Toric.ExponentSystem.Trivialization.ofAtlasMap _ _
    upperAtlas ofOpens_upperHalfPlane_mem_upperAtlas_source

/-- Left of the vertical axis, the frame of `upperHalfPlaneTrivialization` in the chart at a
point is the shear `upperExponent`. -/
theorem upperHalfPlaneTrivialization_frame_of_neg {p : upperHalfPlane} (hp : p.val.val.1 < 0) :
    (upperHalfPlaneTrivialization h).frame (achart (ℝ × ℝ) p) p (mem_achart_source _ p) =
      upperExponent.toAddEquiv := by
  rw [upperHalfPlaneTrivialization, Toric.ExponentSystem.Trivialization.ofAtlasMap_frame,
    exponentSystem_coordChange_of_mem h ⟨((AtlasMap.ofOpens upperHalfPlane).mem_source_iff _).mp
      (mem_achart_source _ p), ofOpens_upperHalfPlane_mem_upperAtlas_source p⟩,
    (atlasIndex_eq_false_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_ne_zero hp.ne),
    atlasIndex_upperAtlas, AtlasMap.coe_ofOpens,
    latticeTransition_false_true_of_neg _ hp]

/-- The upper chart, as a developing map of the upper half-plane with its restricted atlas. -/
noncomputable def upperHalfPlaneDevelopingMap : Toric.DevelopingMap h upperHalfPlane :=
  Toric.DevelopingMap.ofAtlasMap (AtlasMap.ofOpens upperHalfPlane)
    upperAtlas ofOpens_upperHalfPlane_mem_upperAtlas_source

/-- The developing map of the upper half-plane is `(u, v) ↦ (u, v - min u 0)`. -/
@[simp]
theorem upperHalfPlaneDevelopingMap_apply (p : upperHalfPlane) :
    upperHalfPlaneDevelopingMap h p = (p.val.val.1, p.val.val.2 - min p.val.val.1 0) := by
  rw [upperHalfPlaneDevelopingMap, Toric.DevelopingMap.ofAtlasMap_apply, upperAtlas_val,
    AtlasMap.coe_ofOpens, upperChart_apply]

/-- Left of the vertical axis, the tangent frame of `upperHalfPlaneDevelopingMap` in the chart at
a point is the shear `upperTangent`. -/
theorem tangentFrame_upperHalfPlaneDevelopingMap_of_neg {p : upperHalfPlane}
    (hp : p.val.val.1 < 0) :
    (upperHalfPlaneDevelopingMap h).tangentFrame (achart (ℝ × ℝ) p) p (mem_achart_source _ p) =
      upperTangent.toAddEquiv := by
  rw [upperHalfPlaneDevelopingMap, Toric.DevelopingMap.tangentFrame_ofAtlasMap,
    tangentLatticeChange_eq_latticeTransition h
      ⟨((AtlasMap.ofOpens upperHalfPlane).mem_source_iff _).mp (mem_achart_source _ p),
        ofOpens_upperHalfPlane_mem_upperAtlas_source p⟩,
    (atlasIndex_eq_false_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_ne_zero hp.ne),
    atlasIndex_upperAtlas, AtlasMap.coe_ofOpens,
    latticeTransition_false_true_of_neg _ hp]

end Mei.FocusFocus
