/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.AtlasMap
public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem.Basic

/-!
# Pullback of exponent systems along atlas maps

Let `f : Mei.AtlasMap V B' B` be a map of integral-affine charted spaces along which every
chart of `B'` is the pullback of a chart of `B`. Every chart change of `B'` is then a
restriction of a chart change of `B`, so the tangent frame change between two charts of `B'`
at `x` is the tangent frame change between their charts of `B` at `f x`
(`Mei.AtlasMap.tangentLatticeChange_chart`). The same holds for the target charts under two
atlas maps with the same underlying map (`Mei.AtlasMap.tangentLatticeChange_chart_of_coe_eq`);
in particular the tangent frame change between the target charts of one chart under two such
maps is the identity (`Mei.AtlasMap.tangentLatticeChange_chart_chart_of_coe_eq`).

An exponent system on `B` therefore pulls back to `B'`
(`Mei.Toric.ExponentSystem.comap`): its frame changes and projections in a chart of `B'` are
those of the corresponding chart of `B`, read at the image point. Pullback is functorial
(`Mei.Toric.ExponentSystem.comap_id`, `Mei.Toric.ExponentSystem.comap_comp`) and carries the
tangent exponent system of `B` to that of `B'` (`Mei.Toric.ExponentSystem.comap_tangent`).
Along `Mei.AtlasMap.ofOpens` it is the restriction of an exponent system to an open subset with
its restricted atlas, relative to the chosen ambient chart of each restricted chart; the
pullbacks along different choices are canonically isomorphic
(`Mei.Toric.ExponentSystem.comapCongr`).

Restriction of lattice local systems over integral-affine manifolds to open subsets is used
throughout Gross–Siebert, *An Invitation to Toric Degenerations*, §2 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
§§1 and 3 (arXiv:1601.07081v4).
-/

public section

open Set Topology Manifold

namespace Mei.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {B B' B'' : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [HasGroupoid B (integralAffineGroupoid h)]
  [TopologicalSpace B'] [ChartedSpace V B'] [HasGroupoid B' (integralAffineGroupoid h)]
  [TopologicalSpace B''] [ChartedSpace V B''] [HasGroupoid B'' (integralAffineGroupoid h)]

/-- For two atlas maps `f` and `g` with the same underlying map, the tangent frame change from
the target chart of `e` under `f` to the target chart of `e'` under `g` at the image of a point
is the tangent frame change from `e` to `e'` at the point. -/
theorem _root_.Mei.AtlasMap.tangentLatticeChange_chart_of_coe_eq (f g : AtlasMap V B' B)
    (hfg : ⇑f = ⇑g) (e e' : atlas V B') (x : B') :
    tangentLatticeChange h (f.chart e) (g.chart e') (f x) = tangentLatticeChange h e e' x := by
  have hmem : x ∈ e.val.source ∩ e'.val.source ↔
      f x ∈ (f.chart e).val.source ∩ (g.chart e').val.source := by
    rw [mem_inter_iff, mem_inter_iff, f.mem_source_iff e, g.mem_source_iff e', hfg]
  by_cases hx : x ∈ e.val.source ∩ e'.val.source
  · obtain ⟨a, u, hu, hxu, ha, hT⟩ := exists_tangentLatticeChange_eq (h := h) (hmem.mp hx)
    refine hT.trans (tangentLatticeChange_eq hx hu (by rwa [f.apply_eq e hx.1]) ?_).symm
    intro y hy
    rw [f.symm_trans_eqOn_of_coe_eq g hfg e e' hy.1]
    exact ha ⟨f.symm_trans_source_subset_of_coe_eq g hfg e e' hy.1, hy.2⟩
  · rw [tangentLatticeChange_of_notMem hx, tangentLatticeChange_of_notMem (mt hmem.mpr hx)]

/-- Along an atlas map, the tangent frame change between the target charts of two charts at
the image of a point is the tangent frame change between the two charts at the point. -/
@[simp]
theorem _root_.Mei.AtlasMap.tangentLatticeChange_chart (f : AtlasMap V B' B)
    (e e' : atlas V B') (x : B') :
    tangentLatticeChange h (f.chart e) (f.chart e') (f x) = tangentLatticeChange h e e' x :=
  f.tangentLatticeChange_chart_of_coe_eq f rfl e e' x

/-- For two atlas maps with the same underlying map, at a point of the domain of a chart, the
tangent frame change between the target charts of that chart under the two maps is the
identity. -/
theorem _root_.Mei.AtlasMap.tangentLatticeChange_chart_chart_of_coe_eq (f g : AtlasMap V B' B)
    (hfg : ⇑f = ⇑g) (e : atlas V B') {x : B'} (hx : x ∈ e.val.source) :
    tangentLatticeChange h (f.chart e) (g.chart e) (f x) = AddEquiv.refl N := by
  rw [f.tangentLatticeChange_chart_of_coe_eq g hfg, tangentLatticeChange_self hx]

namespace ExponentSystem

variable {Γ : Type*} [AddCommGroup Γ] (E : ExponentSystem h B Γ)

/-- The pullback of an exponent system along an atlas map: the frame change between two
charts at a point is the frame change between their target charts at the image point, and the
projection in a chart is the projection in its target chart. -/
def comap (f : AtlasMap V B' B) : ExponentSystem h B' Γ where
  coordChange e e' x := E.coordChange (f.chart e) (f.chart e') (f x)
  coordChange_trans {e e' e'' x} hx := E.coordChange_trans <| by
    rw [mem_inter_iff, f.mem_source_inter_iff, f.mem_source_iff e''] at hx
    exact hx
  eventually_coordChange_eq hx :=
    f.continuous.continuousAt.eventually
      (E.eventually_coordChange_eq ((f.mem_source_inter_iff _ _).mp hx))
  coordChange_of_notMem hx := E.coordChange_of_notMem (mt (f.mem_source_inter_iff _ _).mpr hx)
  projection e := E.projection (f.chart e)
  projection_coordChange {e e' x} hx γ := by
    rw [E.projection_coordChange ((f.mem_source_inter_iff e e').mp hx),
      f.tangentLatticeChange_chart]

/-- The frame changes of a pulled-back exponent system are those of the target charts at the
image point. -/
@[simp]
theorem comap_coordChange (f : AtlasMap V B' B) (e e' : atlas V B') (x : B') :
    (E.comap f).coordChange e e' x = E.coordChange (f.chart e) (f.chart e') (f x) := (rfl)

/-- The projection of a pulled-back exponent system in a chart is that in its target chart. -/
@[simp]
theorem comap_projection (f : AtlasMap V B' B) (e : atlas V B') :
    (E.comap f).projection e = E.projection (f.chart e) := (rfl)

/-- Pulling back along the identity atlas map does nothing. -/
@[simp]
theorem comap_id : E.comap (AtlasMap.id V B) = E := by
  ext <;> simp

/-- Pulling back along a composite of atlas maps is pulling back in two steps. -/
theorem comap_comp (g : AtlasMap V B' B) (f : AtlasMap V B'' B') :
    E.comap (g.comp f) = (E.comap g).comap f := by
  ext <;> simp

/-- The pullback of the tangent exponent system along an atlas map is the tangent exponent
system of the source. -/
@[simp]
theorem comap_tangent (f : AtlasMap V B' B) : (tangent h B).comap f = tangent h B' := by
  ext <;> simp

end ExponentSystem

end Mei.Toric
