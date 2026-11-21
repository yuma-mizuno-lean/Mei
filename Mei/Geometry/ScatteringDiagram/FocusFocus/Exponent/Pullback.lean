/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.Pullback
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exponent.System

/-!
# Pullbacks of the focus-focus exponent system

Let `f : Mei.AtlasMap (ℝ × ℝ) B regularLocus` be an atlas map into the punctured plane with its
focus-focus atlas. On overlaps, the frame changes of the pulled-back exponent system
`(exponentSystem h).comap f` are the `upperExponent` transitions between the indices of the
target charts, read at the image point (`Mei.FocusFocus.exponentSystem_comap_coordChange_of_mem`),
and the tangent frame changes of `B` are the corresponding `upperTangent` transitions
(`Mei.FocusFocus.tangentLatticeChange_eq_latticeTransition_of_atlasMap`). Over the closed
right half-plane all of these frame changes are the identity.

In particular, on the right chamber `rightChamber` (`u > 0`) with its restricted atlas, the
restricted exponent system and the integral tangent lattice have only identity frame changes
(`Mei.FocusFocus.exponentSystem_comap_rightChamber_coordChange`,
`Mei.FocusFocus.tangentLatticeChange_rightChamber`). On the upper half-plane `upperHalfPlane`
(`v > 0`), a neighbourhood of the upper slab, the restricted atlas assigns the upper chart to
the charts at points of the slab and the cut chart to those at the other points. There the
frame change from the chart at a point `p` with `u < 0` to the chart at a point of the slab is,
at `p`, the shear `upperExponent`, respectively `upperTangent` on the tangent lattice
(`Mei.FocusFocus.exponentSystem_comap_upperHalfPlane_coordChange`,
`Mei.FocusFocus.tangentLatticeChange_upperHalfPlane`).

The geometry is the focus-focus local model of Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.2–2.3 (arXiv:0808.2749v2).
-/

public section

open Set Topology Manifold TopologicalSpace

namespace Mei.FocusFocus

attribute [local instance] chartedSpace hasGroupoid

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {B : Type*} [TopologicalSpace B] [ChartedSpace (ℝ × ℝ) B]
  [HasGroupoid B (Toric.integralAffineGroupoid h)]

/-- Along an atlas map into the punctured plane, on the overlap of two chart domains, the
frame changes of the pulled-back focus-focus exponent system are the `upperExponent`
transitions between the indices of the target charts at the image point. -/
theorem exponentSystem_comap_coordChange_of_mem (f : AtlasMap (ℝ × ℝ) B regularLocus)
    {e e' : atlas (ℝ × ℝ) B} {x : B} (hx : x ∈ e.val.source ∩ e'.val.source) :
    ((exponentSystem h).comap f).coordChange e e' x =
      latticeTransition upperExponent.toAddEquiv (atlasIndex (f.chart e))
        (atlasIndex (f.chart e')) (f x) := by
  rw [Toric.ExponentSystem.comap_coordChange,
    exponentSystem_coordChange_of_mem h ((f.mem_source_inter_iff e e').mp hx)]

/-- Along an atlas map into the punctured plane, on the overlap of two chart domains, the
tangent frame changes of the source are the `upperTangent` transitions between the indices of
the target charts at the image point. -/
theorem tangentLatticeChange_eq_latticeTransition_of_atlasMap
    (f : AtlasMap (ℝ × ℝ) B regularLocus) {e e' : atlas (ℝ × ℝ) B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    Toric.tangentLatticeChange h e e' x =
      latticeTransition upperTangent.toAddEquiv (atlasIndex (f.chart e))
        (atlasIndex (f.chart e')) (f x) := by
  rw [← f.tangentLatticeChange_chart,
    tangentLatticeChange_eq_latticeTransition h ((f.mem_source_inter_iff e e').mp hx)]

/-- Along an atlas map into the punctured plane, at a point mapped to the closed right
half-plane, every frame change of the pulled-back focus-focus exponent system is the
identity. -/
theorem exponentSystem_comap_coordChange_of_nonneg (f : AtlasMap (ℝ × ℝ) B regularLocus)
    (e e' : atlas (ℝ × ℝ) B) {x : B} (hx : 0 ≤ (f x).val.1) :
    ((exponentSystem h).comap f).coordChange e e' x = AddEquiv.refl _ := by
  by_cases hm : x ∈ e.val.source ∩ e'.val.source
  · rw [exponentSystem_comap_coordChange_of_mem h f hm, latticeTransition_of_nonneg _ _ _ hx]
  · exact ((exponentSystem h).comap f).coordChange_of_notMem hm

/-- Along an atlas map into the punctured plane, at a point mapped to the closed right
half-plane, every tangent frame change of the source is the identity. -/
theorem tangentLatticeChange_of_nonneg (f : AtlasMap (ℝ × ℝ) B regularLocus)
    (e e' : atlas (ℝ × ℝ) B) {x : B} (hx : 0 ≤ (f x).val.1) :
    Toric.tangentLatticeChange h e e' x = AddEquiv.refl _ := by
  by_cases hm : x ∈ e.val.source ∩ e'.val.source
  · rw [tangentLatticeChange_eq_latticeTransition_of_atlasMap h f hm,
      latticeTransition_of_nonneg _ _ _ hx]
  · exact Toric.tangentLatticeChange_of_notMem hm

/-- The right chamber `u > 0` of the punctured plane. -/
def rightChamber : Opens regularLocus :=
  ⟨{p | 0 < p.val.1}, isOpen_lt continuous_const continuous_subtypeVal.fst⟩

/-- A point of the punctured plane lies in the right chamber exactly when `u > 0`. -/
@[simp]
theorem mem_rightChamber (p : regularLocus) : p ∈ rightChamber ↔ 0 < p.val.1 := by
  rw [rightChamber, Opens.mem_mk, mem_ofPred_eq]

/-- On the right chamber with its restricted atlas, every frame change of the restriction of
the focus-focus exponent system is the identity. -/
theorem exponentSystem_comap_rightChamber_coordChange (e e' : atlas (ℝ × ℝ) rightChamber)
    (p : rightChamber) :
    ((exponentSystem h).comap (AtlasMap.ofOpens rightChamber)).coordChange e e' p =
      AddEquiv.refl _ :=
  exponentSystem_comap_coordChange_of_nonneg h _ e e' <| by
    rw [AtlasMap.coe_ofOpens]
    exact p.property.le

/-- On the right chamber with its restricted atlas, every tangent frame change is the
identity. -/
theorem tangentLatticeChange_rightChamber (e e' : atlas (ℝ × ℝ) rightChamber)
    (p : rightChamber) : Toric.tangentLatticeChange h e e' p = AddEquiv.refl _ :=
  tangentLatticeChange_of_nonneg h (AtlasMap.ofOpens rightChamber) e e' <| by
    rw [AtlasMap.coe_ofOpens]
    exact p.property.le

/-- The upper half-plane `v > 0` of the punctured plane, a neighbourhood of the upper slab. -/
def upperHalfPlane : Opens regularLocus :=
  ⟨{p | 0 < p.val.2}, isOpen_lt continuous_const continuous_subtypeVal.snd⟩

/-- A point of the punctured plane lies in the upper half-plane exactly when `v > 0`. -/
@[simp]
theorem mem_upperHalfPlane (p : regularLocus) : p ∈ upperHalfPlane ↔ 0 < p.val.2 := by
  rw [upperHalfPlane, Opens.mem_mk, mem_ofPred_eq]

/-- In the restricted atlas of the upper half-plane, the chart at a point of the upper slab
`u = 0` is assigned the upper chart. -/
theorem ofOpens_upperHalfPlane_chart_achart_of_eq_zero {q : upperHalfPlane}
    (hq : q.val.val.1 = 0) :
    ((AtlasMap.ofOpens upperHalfPlane).chart (achart (ℝ × ℝ) q)).val = upperChart := by
  have hqc := ((AtlasMap.ofOpens upperHalfPlane).mem_source_iff (achart (ℝ × ℝ) q)).mp
    (mem_chart_source _ q)
  rw [AtlasMap.coe_ofOpens] at hqc
  rcases (mem_atlas_iff _).mp ((AtlasMap.ofOpens upperHalfPlane).chart (achart (ℝ × ℝ) q)).property
    with hc | hc
  · rw [hc, mem_cutChart_source, hq] at hqc
    exact absurd hqc
      (by simpa only [ne_eq, not_true_eq_false, false_or, not_lt] using q.property.le)
  · exact hc

/-- In the restricted atlas of the upper half-plane, the chart at a point off the vertical axis
is assigned the cut chart. -/
theorem ofOpens_upperHalfPlane_chart_achart_of_ne_zero {p : upperHalfPlane}
    (hp : p.val.val.1 ≠ 0) :
    ((AtlasMap.ofOpens upperHalfPlane).chart (achart (ℝ × ℝ) p)).val = cutChart := by
  let q : upperHalfPlane := ⟨⟨(0, 1), by simp⟩, by simp⟩
  have hq : q ∉ (achart (ℝ × ℝ) p).val.source := by
    rw [achart_val, TopologicalSpace.Opens.chartAt_eq,
      chartAt_of_mem_cutChart_source ((mem_cutChart_source _).mpr (Or.inl hp)),
      OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, mem_cutChart_source]
    norm_num [q]
  rcases (mem_atlas_iff _).mp ((AtlasMap.ofOpens upperHalfPlane).chart (achart (ℝ × ℝ) p)).property
    with hc | hc
  · exact hc
  · refine absurd ?_ hq
    rw [(AtlasMap.ofOpens upperHalfPlane).mem_source_iff, AtlasMap.coe_ofOpens, hc,
      mem_upperChart_source]
    norm_num [q]

/-- In the restricted atlas of the upper half-plane, every point lies in the domains of its own
chart and of the chart at any point of the upper slab. -/
theorem mem_achart_source_inter_upperHalfPlane {p q : upperHalfPlane} (hq : q.val.val.1 = 0) :
    p ∈ (achart (ℝ × ℝ) p).val.source ∩ (achart (ℝ × ℝ) q).val.source := by
  refine ⟨mem_chart_source _ p, ?_⟩
  rw [(AtlasMap.ofOpens upperHalfPlane).mem_source_iff, AtlasMap.coe_ofOpens,
    ofOpens_upperHalfPlane_chart_achart_of_eq_zero hq, mem_upperChart_source]
  exact p.property

/-- On the upper half-plane with its restricted atlas, the frame change of the restricted
focus-focus exponent system from the chart at a point `p` left of the vertical axis to the
chart at a point of the upper slab is, at `p`, the upper exponent shear. -/
theorem exponentSystem_comap_upperHalfPlane_coordChange {p q : upperHalfPlane}
    (hp : p.val.val.1 < 0) (hq : q.val.val.1 = 0) :
    ((exponentSystem h).comap (AtlasMap.ofOpens upperHalfPlane)).coordChange
      (achart (ℝ × ℝ) p) (achart (ℝ × ℝ) q) p = upperExponent.toAddEquiv := by
  rw [exponentSystem_comap_coordChange_of_mem h _ (mem_achart_source_inter_upperHalfPlane hq),
    (atlasIndex_eq_false_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_ne_zero hp.ne),
    (atlasIndex_eq_true_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_eq_zero hq),
    AtlasMap.coe_ofOpens, latticeTransition_false_true_of_neg _ hp]

/-- On the upper half-plane with its restricted atlas, the tangent frame change from the chart
at a point `p` left of the vertical axis to the chart at a point of the upper slab is, at `p`,
the upper tangent shear. -/
theorem tangentLatticeChange_upperHalfPlane {p q : upperHalfPlane}
    (hp : p.val.val.1 < 0) (hq : q.val.val.1 = 0) :
    Toric.tangentLatticeChange h (achart (ℝ × ℝ) p) (achart (ℝ × ℝ) q) p =
      upperTangent.toAddEquiv := by
  rw [tangentLatticeChange_eq_latticeTransition_of_atlasMap h (AtlasMap.ofOpens upperHalfPlane)
      (mem_achart_source_inter_upperHalfPlane hq),
    (atlasIndex_eq_false_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_ne_zero hp.ne),
    (atlasIndex_eq_true_iff _).mpr (ofOpens_upperHalfPlane_chart_achart_of_eq_zero hq),
    AtlasMap.coe_ofOpens, latticeTransition_false_true_of_neg _ hp]

end Mei.FocusFocus
