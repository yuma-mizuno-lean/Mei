/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Maps of charted spaces that pull back charts

An atlas map `f : Mei.AtlasMap H M M'` between charted spaces modelled on `H` is a map
`f : M → M'` with a chart `f.chart e` of `M'` for each chart `e` of `M`, such that `e` is the
pullback of `f.chart e` along `f`: the domain of `e` is the preimage of the domain of
`f.chart e`, and `e = f.chart e ∘ f` there. Dually, the target of `e` lies in the target of
`f.chart e` (`Mei.AtlasMap.target_subset_chart_target`), and on it
`f ∘ e⁻¹ = (f.chart e)⁻¹` (`Mei.AtlasMap.apply_symm_eq_chart_symm`). Such a map is continuous
(`Mei.AtlasMap.continuous`), and every chart change `e⁻¹ ≫ e'` of `M` is the restriction of the
chart change of the corresponding charts of `M'` (`Mei.AtlasMap.symm_trans_eqOn`); hence `M`
inherits every structure groupoid of `M'` that is closed under restriction
(`Mei.AtlasMap.hasGroupoid`). More generally, for two atlas maps with the same underlying map,
every chart change of `M` is the restriction of the chart change from the target chart of the
first chart under the first map to the target chart of the second chart under the second map
(`Mei.AtlasMap.symm_trans_eqOn_of_coe_eq`).

Atlas maps compose (`Mei.AtlasMap.comp`) with identities (`Mei.AtlasMap.id`). The inclusion of
an open subset with Mathlib's restricted atlas `TopologicalSpace.Opens.instChartedSpace` is an
atlas map (`Mei.AtlasMap.ofOpens`); its charts are chosen restrictions of charts of the ambient
space.

Data indexed by the charts of an atlas pull back along atlas maps; for exponent systems this is
`Mei.Toric.ExponentSystem.comap`.
-/

public section

open Set Topology TopologicalSpace Manifold

namespace Mei

/-- A map `M → M'` of charted spaces modelled on `H`, together with a chart of `M'` for each
chart of `M`, such that each chart of `M` is the pullback of its chart of `M'`: its domain is
the preimage of the domain of the chart of `M'`, and on it the chart of `M` is the chart of
`M'` composed with the map. -/
structure AtlasMap (H : Type*) [TopologicalSpace H] (M M' : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H M'] where
  /-- The underlying map. -/
  toFun : M → M'
  /-- The chart of the target of which a chart of the source is the pullback. -/
  chart : atlas H M → atlas H M'
  /-- The domain of a chart is the preimage of the domain of its target chart. -/
  source_eq (e : atlas H M) : e.1.source = toFun ⁻¹' (chart e).1.source
  /-- On its domain, a chart is its target chart composed with the map. -/
  apply_eq (e : atlas H M) {x : M} : x ∈ e.1.source → e.1 x = (chart e).1 (toFun x)

namespace AtlasMap

variable {H : Type*} [TopologicalSpace H]
  {M M' M'' M''' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H M'] [TopologicalSpace M''] [ChartedSpace H M'']
  [TopologicalSpace M'''] [ChartedSpace H M''']

instance : CoeFun (AtlasMap H M M') fun _ => M → M' :=
  ⟨toFun⟩

/-- Two atlas maps are equal when their underlying maps and their chart assignments agree. -/
@[ext]
theorem ext {f g : AtlasMap H M M'} (h₁ : ∀ x, f x = g x) (h₂ : ∀ e, f.chart e = g.chart e) :
    f = g := by
  rcases f with ⟨f, c, _, _⟩
  rcases g with ⟨g, c', _, _⟩
  obtain rfl : f = g := funext h₁
  obtain rfl : c = c' := funext h₂
  rfl

variable (f : AtlasMap H M M')

/-- A point lies in the domain of a chart exactly when its image lies in the domain of the
target chart. -/
theorem mem_source_iff (e : atlas H M) {x : M} :
    x ∈ e.1.source ↔ f x ∈ (f.chart e).1.source := by
  rw [f.source_eq e, mem_preimage]

/-- A point lies in the overlap of two chart domains exactly when its image lies in the
overlap of the domains of their target charts. -/
theorem mem_source_inter_iff (e e' : atlas H M) {x : M} :
    x ∈ e.1.source ∩ e'.1.source ↔ f x ∈ (f.chart e).1.source ∩ (f.chart e').1.source := by
  rw [mem_inter_iff, mem_inter_iff, f.mem_source_iff e, f.mem_source_iff e']

/-- For two atlas maps with the same underlying map, at a point of the domain of a chart, the
image point lies in the domains of the target charts of that chart under both maps. -/
theorem mem_chart_source_inter_of_coe_eq {f g : AtlasMap H M M'} (hfg : ⇑f = ⇑g)
    {e : atlas H M} {x : M} (hx : x ∈ e.1.source) :
    f x ∈ (f.chart e).1.source ∩ (g.chart e).1.source :=
  ⟨(f.mem_source_iff e).mp hx, by rw [hfg]; exact (g.mem_source_iff e).mp hx⟩

/-- On its domain, a chart is its target chart composed with the map. -/
theorem chart_apply (e : atlas H M) {x : M} (hx : x ∈ e.1.source) :
    (f.chart e).1 (f x) = e.1 x :=
  (f.apply_eq e hx).symm

/-- On the domain of a chart, the map is the inverse of the target chart composed with the
chart. -/
theorem chart_symm_apply (e : atlas H M) {x : M} (hx : x ∈ e.1.source) :
    (f.chart e).1.symm (e.1 x) = f x := by
  rw [← f.chart_apply e hx, OpenPartialHomeomorph.left_inv _ ((f.mem_source_iff e).mp hx)]

/-- The target of a chart is contained in the target of its target chart. -/
theorem target_subset_chart_target (e : atlas H M) : e.1.target ⊆ (f.chart e).1.target := by
  intro y hy
  rw [← e.1.right_inv hy, ← f.chart_apply e (e.1.map_target hy)]
  exact (f.chart e).1.map_source ((f.mem_source_iff e).mp (e.1.map_target hy))

/-- On the target of a chart, the map composed with the inverse chart is the inverse of the
target chart. -/
theorem apply_symm_eq_chart_symm (e : atlas H M) {y : H} (hy : y ∈ e.1.target) :
    f (e.1.symm y) = (f.chart e).1.symm y := by
  rw [← f.chart_symm_apply e (e.1.map_target hy), e.1.right_inv hy]

/-- An atlas map is continuous. -/
@[fun_prop]
theorem continuous : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hx := mem_chart_source H x
  have hc : ContinuousAt (f.chart (achart H x)).1.symm ((achart H x).1 x) := by
    rw [← f.chart_apply _ hx]
    exact (f.chart _).1.continuousAt_symm
      ((f.chart _).1.map_source ((f.mem_source_iff (achart H x)).mp hx))
  refine (hc.comp ((achart H x).1.continuousAt hx)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x).open_source.mem_nhds hx] with y hy
  exact (f.chart_symm_apply (achart H x) hy).symm

/-- For two atlas maps with the same underlying map, the chart change between two charts of
the source is defined wherever the chart change from the target chart of the first chart under
the first map to the target chart of the second chart under the second map is. -/
theorem symm_trans_source_subset_of_coe_eq (g : AtlasMap H M M') (hfg : ⇑f = ⇑g)
    (e e' : atlas H M) :
    (e.1.symm ≫ₕ e'.1).source ⊆ ((f.chart e).1.symm ≫ₕ (g.chart e').1).source := by
  intro y hy
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy ⊢
  refine ⟨f.target_subset_chart_target e hy.1, ?_⟩
  rw [mem_preimage, ← f.apply_symm_eq_chart_symm e hy.1, hfg]
  exact (g.mem_source_iff e').mp hy.2

/-- The chart change between two charts of the source is defined wherever the chart change
between their target charts is. -/
theorem symm_trans_source_subset (e e' : atlas H M) :
    (e.1.symm ≫ₕ e'.1).source ⊆ ((f.chart e).1.symm ≫ₕ (f.chart e').1).source :=
  f.symm_trans_source_subset_of_coe_eq f rfl e e'

/-- For two atlas maps with the same underlying map, the chart change between two charts of
the source is the restriction of the chart change from the target chart of the first chart
under the first map to the target chart of the second chart under the second map. -/
theorem symm_trans_eqOn_of_coe_eq (g : AtlasMap H M M') (hfg : ⇑f = ⇑g) (e e' : atlas H M) :
    EqOn (e.1.symm ≫ₕ e'.1) ((f.chart e).1.symm ≫ₕ (g.chart e').1)
      (e.1.symm ≫ₕ e'.1).source := by
  intro y hy
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
  rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
    ← f.apply_symm_eq_chart_symm e hy.1, hfg, g.chart_apply e' hy.2]

/-- The chart change between two charts of the source is the restriction of the chart change
between their target charts. -/
theorem symm_trans_eqOn (e e' : atlas H M) :
    EqOn (e.1.symm ≫ₕ e'.1) ((f.chart e).1.symm ≫ₕ (f.chart e').1)
      (e.1.symm ≫ₕ e'.1).source :=
  f.symm_trans_eqOn_of_coe_eq f rfl e e'

include f in
/-- If the chart changes of the target lie in a groupoid closed under restriction, then so do
those of the source. -/
theorem hasGroupoid {G : StructureGroupoid H} [ClosedUnderRestriction G] [HasGroupoid M' G] :
    HasGroupoid M G where
  compatible {e e'} he he' := by
    have hm := G.restr_mem_of_eqOn
      (G.compatible (f.chart ⟨e, he⟩).2 (f.chart ⟨e', he'⟩).2) (e.symm ≫ₕ e').open_source
      (f.symm_trans_eqOn ⟨e, he⟩ ⟨e', he'⟩).symm
      (inter_subset_left.trans (f.symm_trans_source_subset ⟨e, he⟩ ⟨e', he'⟩))
    rwa [OpenPartialHomeomorph.restr_eq_of_source_subset subset_rfl] at hm

variable (H M) in
/-- The identity atlas map, assigning each chart to itself. -/
protected def id : AtlasMap H M M where
  toFun := _root_.id
  chart := _root_.id
  source_eq e := by rw [id_eq, preimage_id_eq, id_eq]
  apply_eq e x _ := by rw [id_eq, id_eq]

/-- The identity atlas map is the identity. -/
@[simp]
theorem coe_id : ⇑(AtlasMap.id H M) = _root_.id := (rfl)

/-- The identity atlas map assigns each chart to itself. -/
@[simp]
theorem id_chart (e : atlas H M) : (AtlasMap.id H M).chart e = e := (rfl)

/-- The composite of two atlas maps, assigning to a chart the target chart of its target
chart. -/
def comp (g : AtlasMap H M' M'') (f : AtlasMap H M M') : AtlasMap H M M'' where
  toFun := g ∘ f
  chart := g.chart ∘ f.chart
  source_eq e := by
    ext x
    rw [Function.comp_apply, mem_preimage, Function.comp_apply, f.mem_source_iff e,
      g.mem_source_iff]
  apply_eq e _ hx := by
    rw [Function.comp_apply, Function.comp_apply, g.chart_apply _ ((f.mem_source_iff e).mp hx),
      f.chart_apply e hx]

/-- The composite of two atlas maps is the composite of the underlying maps. -/
@[simp]
theorem coe_comp (g : AtlasMap H M' M'') (f : AtlasMap H M M') : ⇑(g.comp f) = g ∘ f := (rfl)

/-- The composite of two atlas maps composes the chart assignments. -/
@[simp]
theorem comp_chart (g : AtlasMap H M' M'') (f : AtlasMap H M M') (e : atlas H M) :
    (g.comp f).chart e = g.chart (f.chart e) := (rfl)

/-- Composing with the identity on the left does nothing. -/
@[simp]
theorem id_comp : (AtlasMap.id H M').comp f = f := by
  ext <;> simp

/-- Composing with the identity on the right does nothing. -/
@[simp]
theorem comp_id : f.comp (AtlasMap.id H M) = f := by
  ext <;> simp

/-- Composition of atlas maps is associative. -/
theorem comp_assoc (k : AtlasMap H M'' M''') (g : AtlasMap H M' M'') :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext <;> simp

/-- The inclusion of an open subset, with the restricted atlas
`TopologicalSpace.Opens.instChartedSpace`, as an atlas map: each chart of the open subset is
assigned a chart of the ambient space of which it is the restriction. The assignment is a
choice, since different charts may have the same restriction. -/
noncomputable def ofOpens (s : Opens M) : AtlasMap H s M where
  toFun := (↑)
  chart e := achart H (mem_iUnion.mp e.2).choose.1
  source_eq e := by
    conv_lhs => rw [mem_singleton_iff.mp (mem_iUnion.mp e.2).choose_spec]
    rw [OpenPartialHomeomorph.subtypeRestr_source, achart_val]
  apply_eq e x _ := by
    conv_lhs => rw [mem_singleton_iff.mp (mem_iUnion.mp e.2).choose_spec]
    rw [OpenPartialHomeomorph.subtypeRestr_coe, domRestrict_apply, achart_val]

/-- The inclusion of an open subset is the subtype inclusion. -/
@[simp]
theorem coe_ofOpens (s : Opens M) : ⇑(ofOpens (H := H) s) = Subtype.val := (rfl)

/-- Each chart of an open subset is the restriction of its assigned chart of the ambient
space. -/
@[simp]
theorem subtypeRestr_ofOpens_chart {s : Opens M} (e : atlas H s) (hs : Nonempty s) :
    ((ofOpens s).chart e).1.subtypeRestr hs = e.1 :=
  (mem_singleton_iff.mp (mem_iUnion.mp e.2).choose_spec).symm

end AtlasMap

end Mei
