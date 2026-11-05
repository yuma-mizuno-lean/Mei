/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.Basic
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Exponent.Basic
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# The integral-affine atlas of the focus-focus puncture

The punctured plane carries two charts. The cut chart is the identity away from
the nonnegative vertical ray. The upper chart crosses that ray and sends
`(u,v)` to `(u,v - min u 0)`. On the upper left overlap the change of coordinates
is the integral shear `(u,v) ↦ (u,v-u)`; on the upper right it is the identity.
Thus the chamber coordinates agree across the lower slab and differ by the
specified shear across the upper slab. As elements of the atlas the two charts are
`cutAtlas` and `upperAtlas`, and both chart domains are preconnected
(`isPreconnected_source`).

`chartedSpace` and `hasGroupoid` equip the actual punctured plane with this
integral-affine structure. The charted-space definition is explicit, so a caller
can select this atlas without replacing the usual smooth atlas on an open subset
of the plane. The shear's lattice map is `upperTangent`, whose compatibility
with `upperExponent` and `exponentProjection` is proved in the exponent module.

The construction uses Mathlib's `Equiv.prodShear` and
`OpenPartialHomeomorph.subtypeRestr`, and Mei's
`Toric.IntegralAffineEquiv.ofLatticeEquiv` and `Toric.integralAffineGroupoid`.
The geometry is the focus-focus local model of
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open Set TopologicalSpace

/-- The nonsingular locus of the focus-focus plane. -/
def regularLocus : Opens (ℝ × ℝ) := ⟨{p | p ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

/-- Points of the regular locus are exactly the nonzero points of the plane. -/
@[simp] theorem mem_regularLocus (p : ℝ × ℝ) : p ∈ regularLocus ↔ p ≠ 0 := Iff.rfl

private theorem regularLocus_nonempty : Nonempty regularLocus :=
  ⟨⟨(1, 0), by simp⟩⟩

private def cutDomain : Set (ℝ × ℝ) := {p | p.1 ≠ 0 ∨ p.2 < 0}

private theorem isOpen_cutDomain : IsOpen cutDomain :=
  (isOpen_ne_fun continuous_fst continuous_const).union (isOpen_lt continuous_snd continuous_const)

private def upperChartHomeomorph : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  { Equiv.prodShear (Equiv.refl ℝ) (fun u => Equiv.subRight (min u 0)) with
    continuous_toFun := continuous_fst.prodMk
      (continuous_snd.sub (continuous_fst.min continuous_const))
    continuous_invFun := continuous_fst.prodMk
      (continuous_snd.add (continuous_fst.min continuous_const)) }

private def cutPlaneChart : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  OpenPartialHomeomorph.ofSet cutDomain isOpen_cutDomain

private def upperPlaneChart : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  (OpenPartialHomeomorph.ofSet {p : ℝ × ℝ | 0 < p.2}
    (isOpen_lt continuous_const continuous_snd)).trans upperChartHomeomorph.toOpenPartialHomeomorph

/-- The identity chart on the punctured plane cut along the upper vertical ray. -/
def cutChart : OpenPartialHomeomorph regularLocus (ℝ × ℝ) :=
  cutPlaneChart.subtypeRestr regularLocus_nonempty

/-- The chart extending across the upper slab, with a shear on its left half. -/
def upperChart : OpenPartialHomeomorph regularLocus (ℝ × ℝ) :=
  upperPlaneChart.subtypeRestr regularLocus_nonempty

/-- The cut chart is defined on both chambers and on the lower slab. -/
@[simp] theorem mem_cutChart_source (p : regularLocus) :
    p ∈ cutChart.source ↔ p.val.1 ≠ 0 ∨ p.val.2 < 0 := by
  simp [cutChart, cutPlaneChart, cutDomain]

/-- The upper chart is defined on the upper half-plane. -/
@[simp] theorem mem_upperChart_source (p : regularLocus) :
    p ∈ upperChart.source ↔ 0 < p.val.2 := by
  simp [upperChart, upperPlaneChart]

@[simp] theorem cutChart_apply (p : regularLocus) : cutChart p = p.val := (rfl)

@[simp] theorem upperChart_apply (p : regularLocus) :
    upperChart p = (p.val.1, p.val.2 - min p.val.1 0) := (rfl)

/-- The inverse cut chart recovers the point of the plane on its target. -/
@[simp] theorem cutChart_symm_apply (p : ℝ × ℝ) (hp : p ∈ cutChart.target) :
    (cutChart.symm p).val = p := by
  simpa only [cutChart, cutPlaneChart, OpenPartialHomeomorph.ofSet_symm,
    OpenPartialHomeomorph.ofSet_apply, Function.comp_apply, id_eq] using
    cutPlaneChart.subtypeRestr_symm_apply regularLocus_nonempty hp

/-- The upper chart is inverted by adding the same piecewise-linear correction. -/
@[simp] theorem upperChart_symm_apply (p : ℝ × ℝ) (hp : p ∈ upperChart.target) :
    (upperChart.symm p).val = (p.1, p.2 + min p.1 0) := by
  have hi : upperChartHomeomorph.symm p = (p.1, p.2 + min p.1 0) := (rfl)
  simpa [upperChart, upperPlaneChart, hi] using
    upperPlaneChart.subtypeRestr_symm_apply regularLocus_nonempty hp

/-- The cut chart has the same source and target in plane coordinates. -/
@[simp] theorem mem_cutChart_target (p : ℝ × ℝ) :
    p ∈ cutChart.target ↔ p.1 ≠ 0 ∨ p.2 < 0 := by
  constructor
  · intro hp
    have hs := (mem_cutChart_source _).mp (cutChart.map_target hp)
    simpa only [cutChart_symm_apply p hp] using hs
  · intro hp
    have hp0 : p ≠ 0 := by rintro rfl; simp at hp
    simpa only [cutChart_apply] using
      cutChart.map_source ((mem_cutChart_source ⟨p, hp0⟩).mpr hp)

/-- The image of the upper chart, expressed in its output coordinates. -/
@[simp] theorem mem_upperChart_target (p : ℝ × ℝ) :
    p ∈ upperChart.target ↔ 0 < p.2 + min p.1 0 := by
  constructor
  · intro hp
    have hs := (mem_upperChart_source _).mp (upperChart.map_target hp)
    simpa only [upperChart_symm_apply p hp] using hs
  · intro hp
    have hp0 : (p.1, p.2 + min p.1 0) ≠ (0 : ℝ × ℝ) := by
      intro he
      have := congrArg Prod.snd he
      simp only [Prod.snd_zero] at this
      linarith
    have hs := upperChart.map_source
      ((mem_upperChart_source ⟨(p.1, p.2 + min p.1 0), hp0⟩).mpr hp)
    simpa only [upperChart_apply, add_sub_cancel_right] using hs

/-- The overlap in cut-chart coordinates is the upper half-plane minus its vertical axis. -/
theorem mem_cutChart_symm_trans_upperChart_source (p : ℝ × ℝ) :
    p ∈ (cutChart.symm.trans upperChart).source ↔ p.1 ≠ 0 ∧ 0 < p.2 := by
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, OpenPartialHomeomorph.symm_source]
  constructor
  · rintro ⟨hp, hq⟩
    have hv := (mem_upperChart_source _).mp hq
    rw [cutChart_symm_apply p hp] at hv
    exact ⟨((mem_cutChart_target p).mp hp).resolve_right (not_lt.mpr hv.le), hv⟩
  · rintro ⟨hu, hv⟩
    have hp := (mem_cutChart_target p).mpr (Or.inl hu)
    refine ⟨hp, (mem_upperChart_source _).mpr ?_⟩
    simpa only [cutChart_symm_apply p hp] using hv

/-- The transition on the two upper overlap components is the piecewise shear. -/
theorem cutChart_symm_trans_upperChart_apply (p : ℝ × ℝ)
    (hp : p ∈ (cutChart.symm.trans upperChart).source) :
    cutChart.symm.trans upperChart p = (p.1, p.2 - min p.1 0) := by
  rw [OpenPartialHomeomorph.trans_apply, upperChart_apply,
    cutChart_symm_apply p hp.1]

/-- The opposite change of coordinates uses the inverse piecewise shear. -/
theorem upperChart_symm_trans_cutChart_apply (p : ℝ × ℝ)
    (hp : p ∈ (upperChart.symm.trans cutChart).source) :
    upperChart.symm.trans cutChart p = (p.1, p.2 + min p.1 0) := by
  rw [OpenPartialHomeomorph.trans_apply, cutChart_apply, upperChart_symm_apply p hp.1]

/-- Both charts together cover every nonsingular point, including the two slab halves. -/
theorem chart_sources_cover (p : regularLocus) :
    p ∈ cutChart.source ∨ p ∈ upperChart.source := by
  simp only [mem_cutChart_source, mem_upperChart_source]
  by_cases hu : p.val.1 = 0
  · have hv : p.val.2 ≠ 0 := fun hv => p.property (Prod.ext hu hv)
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  · exact Or.inl (Or.inl hu)

/-- The domain of the cut chart is preconnected: in the plane it is the complement of the closed
upper half of the vertical axis, which is star-convex about `(0, -1)`. -/
theorem isPreconnected_cutChart_source : IsPreconnected cutChart.source := by
  have hstar : StarConvex ℝ ((0, -1) : ℝ × ℝ) {p : ℝ × ℝ | p.1 ≠ 0 ∨ p.2 < 0} := by
    intro p hp a b ha hb hab
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one]
    rcases hb.eq_or_lt with rfl | hb
    · exact Or.inr (by linarith)
    rcases hp with hp | hp
    · exact Or.inl (mul_ne_zero hb.ne' hp)
    · exact Or.inr (by nlinarith)
  have hsrc : cutChart.source = Subtype.val ⁻¹' {p : ℝ × ℝ | p.1 ≠ 0 ∨ p.2 < 0} := by
    ext p
    exact mem_cutChart_source p
  rw [hsrc]
  refine (hstar.isPathConnected (Or.inr (by norm_num))).isConnected.isPreconnected
    |>.preimage_of_isOpenMap Subtype.val_injective regularLocus.isOpen.isOpenMap_subtype_val
      fun p hp => ⟨⟨p, ?_⟩, rfl⟩
  rw [mem_regularLocus]
  rintro rfl
  simp at hp

/-- The domain of the upper chart, the upper half-plane, is preconnected. -/
theorem isPreconnected_upperChart_source : IsPreconnected upperChart.source := by
  have hsrc : upperChart.source = Subtype.val ⁻¹' (univ ×ˢ Ioi (0 : ℝ)) := by
    ext p
    simp only [mem_upperChart_source, mem_preimage, mem_prod, mem_univ, mem_Ioi, true_and]
  rw [hsrc]
  refine (isPreconnected_univ.prod isPreconnected_Ioi).preimage_of_isOpenMap
    Subtype.val_injective regularLocus.isOpen.isOpenMap_subtype_val fun p hp => ⟨⟨p, ?_⟩, rfl⟩
  rw [mem_regularLocus]
  rintro rfl
  exact lt_irrefl _ hp.2

/-- The focus-focus atlas on the punctured plane. Choose this charted-space
structure explicitly when using its integral-affine chart changes. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (ℝ × ℝ) regularLocus := by
  classical
  exact
    { atlas := {cutChart, upperChart}
      chartAt p := if p ∈ cutChart.source then cutChart else upperChart
      mem_chart_source p := by
        split_ifs with h
        · exact h
        · exact (chart_sources_cover p).resolve_left h
      chart_mem_atlas p := by split_ifs <;> simp }

/-- The atlas consists exactly of the cut chart and the upper chart. -/
@[simp] theorem mem_atlas_iff (e : OpenPartialHomeomorph regularLocus (ℝ × ℝ)) :
    letI := chartedSpace
    e ∈ atlas (ℝ × ℝ) regularLocus ↔ e = cutChart ∨ e = upperChart := by
  rfl

/-- The cut chart as a chart of the focus-focus atlas. -/
def cutAtlas :
    letI := chartedSpace
    atlas (ℝ × ℝ) regularLocus :=
  ⟨cutChart, (mem_atlas_iff _).mpr (Or.inl rfl)⟩

/-- The upper chart as a chart of the focus-focus atlas. -/
def upperAtlas :
    letI := chartedSpace
    atlas (ℝ × ℝ) regularLocus :=
  ⟨upperChart, (mem_atlas_iff _).mpr (Or.inr rfl)⟩

/-- The underlying chart of `cutAtlas` is the cut chart. -/
@[simp]
theorem cutAtlas_val : cutAtlas.1 = cutChart := (rfl)

/-- The underlying chart of `upperAtlas` is the upper chart. -/
@[simp]
theorem upperAtlas_val : upperAtlas.1 = upperChart := (rfl)

/-- The domain of every chart of the focus-focus atlas is preconnected. -/
theorem isPreconnected_source :
    letI := chartedSpace
    ∀ e : atlas (ℝ × ℝ) regularLocus, IsPreconnected e.1.source := by
  intro e
  rcases (mem_atlas_iff e.1).mp e.2 with he | he <;> rw [he]
  · exact isPreconnected_cutChart_source
  · exact isPreconnected_upperChart_source

open Classical in
/-- The preferred chart at a point is the cut chart on its domain and the upper chart
elsewhere. -/
theorem chartAt_eq (p : regularLocus) :
    letI := chartedSpace
    chartAt (ℝ × ℝ) p = if p ∈ cutChart.source then cutChart else upperChart := by
  rfl

/-- The preferred chart at a point in the domain of the cut chart is the cut chart. -/
theorem chartAt_of_mem_cutChart_source {p : regularLocus} (hp : p ∈ cutChart.source) :
    letI := chartedSpace
    chartAt (ℝ × ℝ) p = cutChart := by
  classical
  rw [chartAt_eq, ite_eq_left hp]

/-- The preferred chart at a point outside the domain of the cut chart is the upper chart. -/
theorem chartAt_of_notMem_cutChart_source {p : regularLocus} (hp : p ∉ cutChart.source) :
    letI := chartedSpace
    chartAt (ℝ × ℝ) p = upperChart := by
  classical
  rw [chartAt_eq, ite_eq_right hp]

variable (h : TauCeti.Toric.IsIntegralLattice
  ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The real upper shear, with its specified integral tangent-lattice map. -/
def upperAffine : Toric.IntegralAffineEquiv h h :=
  Toric.IntegralAffineEquiv.ofLatticeEquiv h h upperTangent.toAddEquiv

@[simp] theorem upperAffine_apply (p : ℝ × ℝ) :
    upperAffine h p = (p.1, p.2 - p.1) := by
  have he := h.eq_extend
    (i' := (Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))
    (f := upperTangent.toAddEquiv.toAddMonoidHom)
    (g := (LinearMap.fst ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ))
    (fun n => by simp)
  rw [upperAffine, Toric.IntegralAffineEquiv.ofLatticeEquiv_apply, ← he]
  rfl

@[simp] theorem upperAffine_latticeEquiv :
    (upperAffine h).latticeEquiv = upperTangent.toAddEquiv := by
  rw [upperAffine, Toric.IntegralAffineEquiv.ofLatticeEquiv_latticeEquiv]

/-- On the left half-plane, the change from the cut chart to the upper chart is the upper
shear `upperAffine`. -/
theorem eqOn_cutChart_symm_trans_upperChart_upperAffine :
    EqOn (cutChart.symm.trans upperChart) (upperAffine h)
      ((cutChart.symm.trans upperChart).source ∩ {q | q.1 < 0}) := by
  intro q hq
  have hq' : q.1 < 0 := hq.2
  rw [cutChart_symm_trans_upperChart_apply q hq.1, upperAffine_apply, min_eq_left hq'.le]

/-- On the right half-plane, the change from the cut chart to the upper chart is the
identity. -/
theorem eqOn_cutChart_symm_trans_upperChart_refl :
    EqOn (cutChart.symm.trans upperChart) (Toric.IntegralAffineEquiv.refl h)
      ((cutChart.symm.trans upperChart).source ∩ {q | 0 < q.1}) := by
  intro q hq
  have hq' : 0 < q.1 := hq.2
  simp only [cutChart_symm_trans_upperChart_apply q hq.1, min_eq_right hq'.le,
    sub_zero, Toric.IntegralAffineEquiv.refl_toAffineEquiv, AffineEquiv.refl_apply]

private theorem cutChart_symm_trans_upperChart_mem :
    cutChart.symm.trans upperChart ∈ Toric.integralAffineGroupoid h := by
  rw [Toric.mem_integralAffineGroupoid_iff_forward, Toric.isLocallyIntegralAffineOn_iff]
  intro p hp
  have hu := ((mem_cutChart_symm_trans_upperChart_source p).mp hp).1
  rcases lt_or_gt_of_ne hu with hu | hu
  · exact ⟨upperAffine h, {q | q.1 < 0}, isOpen_lt continuous_fst continuous_const, hu,
      eqOn_cutChart_symm_trans_upperChart_upperAffine h⟩
  · exact ⟨Toric.IntegralAffineEquiv.refl h, {q | 0 < q.1},
      isOpen_lt continuous_const continuous_fst, hu, eqOn_cutChart_symm_trans_upperChart_refl h⟩

/-- Every change of coordinates in the focus-focus atlas is locally integral affine. -/
theorem hasGroupoid :
    letI := chartedSpace
    HasGroupoid regularLocus (Toric.integralAffineGroupoid h) := by
  let _ := chartedSpace
  constructor
  intro e e' he he'
  rcases (mem_atlas_iff e).mp he with rfl | rfl <;>
    rcases (mem_atlas_iff e').mp he' with rfl | rfl
  · exact (closedUnderRestriction_iff_id_le _).mp inferInstance
      ⟨_, _, cutChart.symm_trans_self⟩
  · exact cutChart_symm_trans_upperChart_mem h
  · simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      (Toric.integralAffineGroupoid h).symm (cutChart_symm_trans_upperChart_mem h)
  · exact (closedUnderRestriction_iff_id_le _).mp inferInstance
      ⟨_, _, upperChart.symm_trans_self⟩

end Mei.FocusFocus
