/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.DevelopingMap
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Topology.FiberBundle.GroupCocycle

/-!
# Developing maps of simply connected integral-affine spaces

A simply connected charted space `B` modelled on `V`, whose chart changes are locally integral
affine for the lattice `N ⊆ V`, has a developing map `B → V`
(`Mei.Toric.DevelopingMap.nonempty_of_simplyConnectedSpace`), and its integral tangent lattice has
a trivialization
(`Mei.Toric.DevelopingMap.nonempty_trivialization_tangent_of_simplyConnectedSpace`).

The developing map is a section of a covering space of germs. The group `G` of integral affine
self-equivalences of `V` is discrete. The chart changes `e ↦ e'` at a point, the integral affine
equivalences agreeing with `e' ∘ e⁻¹` near `e x` (`Mei.Toric.chartChange`), form a `G`-valued
cocycle on the atlas, locally constant by rigidity of integral affine equivalences. The cocycle
defines a fibre bundle with fibre `G`, which is a covering map of `B`. A fibre coordinate `g` at
`x` in a chart `e` stands for the germ `g⁻¹ ∘ e` of a local developing map at `x`; changing the
chart multiplies `g` by the chart change. Since `B` is simply connected, the identity lifts to a
section `s`, and `x ↦ (g_e x)⁻¹ (e x)` is a developing map, independent of the chart `e`.

This is the developing map by analytic continuation, as a lift through a covering space. It
applies to any simply connected cover of an integral-affine manifold that carries an
integral-affine atlas, for instance a universal cover with the pulled-back atlas; neither the
atlas of a universal cover nor the uniqueness of the developing map up to an integral affine
equivalence, and hence the holonomy of deck transformations, is treated here. See Gross–Siebert,
*An Invitation to Toric Degenerations*, §2 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §1 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Topology Bundle Manifold

namespace Mei.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {B : Type*} [TopologicalSpace B] [ChartedSpace V B] [HasGroupoid B (integralAffineGroupoid h)]

namespace DevelopingMap

section GermBundle

variable [TopologicalSpace (IntegralAffineEquiv h h)] [DiscreteTopology (IntegralAffineEquiv h h)]

omit [DiscreteTopology (IntegralAffineEquiv h h)] in
/-- The chart changes of an integral-affine atlas are locally constant, hence continuous for the
discrete topology on the integral affine group. -/
private theorem continuousOn_chartChange (e e' : atlas V B) :
    ContinuousOn (chartChange h e e') (e.1.source ∩ e'.1.source) := fun _ hx =>
  (continuousAt_const.congr_of_eventuallyEq (eventually_chartChange_eq hx)).continuousWithinAt

variable (B) in
/-- The fibre bundle with discrete fibre `G = IntegralAffineEquiv h h` over `B` whose transition
from the chart `e` to the chart `e'` is left multiplication by `chartChange h e e'`. -/
private def germBundleCore : FiberBundleCore (atlas V B) B (IntegralAffineEquiv h h) :=
  letI : ContinuousSMul (IntegralAffineEquiv h h) (IntegralAffineEquiv h h) :=
    ⟨continuous_of_discreteTopology⟩
  TauCeti.fiberBundleCoreOfGroupCocycle (fun e => e.1.source) (chartChange h)
    (fun _ _ _ _ hb => chartChange_trans hb) (IntegralAffineEquiv h h)
    (fun e => e.1.open_source) (fun x => ⟨chartAt V x, chart_mem_atlas V x⟩)
    (fun x => mem_chart_source V x) (continuousOn_chartChange h)

private theorem germBundleCore_baseSet (e : atlas V B) :
    (germBundleCore h B).baseSet e = e.1.source := by
  rw [FiberBundleCore.baseSet_at, germBundleCore,
    TauCeti.fiberBundleCoreOfGroupCocycle_localTriv_baseSet]

private theorem germBundleCore_coordChange (e e' : atlas V B) (x : B)
    (g : IntegralAffineEquiv h h) :
    (germBundleCore h B).coordChange e e' x g = chartChange h e e' x * g := by
  rw [germBundleCore, TauCeti.fiberBundleCoreOfGroupCocycle_coordChange, smul_eq_mul]

/-- The bundle of germs is a covering space of `B`. -/
private theorem isCoveringMap_germBundleCore :
    IsCoveringMap (germBundleCore h B).proj :=
  IsFiberBundle.isCoveringMap fun x =>
    ⟨(germBundleCore h B).localTrivAt x, (germBundleCore h B).mem_localTrivAt_baseSet x⟩

variable {h}

/-- The fibre coordinate of a section of the bundle of germs in the chart `e`. -/
private def germ (s : C(B, (germBundleCore h B).TotalSpace)) (e : atlas V B) (x : B) :
    IntegralAffineEquiv h h :=
  ((germBundleCore h B).localTriv e (s x)).2

/-- Changing the chart multiplies the fibre coordinate of a section by the chart change. -/
private theorem germ_change (s : C(B, (germBundleCore h B).TotalSpace))
    (hs : (germBundleCore h B).proj ∘ s = id) {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    germ s e' x = chartChange h e e' x * germ s e x := by
  have hb : (s x).1 = x := congr_fun hs x
  have h₁ : (s x).1 ∈ (germBundleCore h B).baseSet ((germBundleCore h B).indexAt (s x).1) ∩
      (germBundleCore h B).baseSet e ∩ (germBundleCore h B).baseSet e' :=
    ⟨⟨(germBundleCore h B).mem_baseSet_at _, by rw [germBundleCore_baseSet, hb]; exact hx.1⟩,
      by rw [germBundleCore_baseSet, hb]; exact hx.2⟩
  rw [germ, germ, FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
  refine ((germBundleCore h B).coordChange_comp _ e e' _ h₁ (s x).2).symm.trans ?_
  rw [germBundleCore_coordChange, hb]

/-- The fibre coordinate of a continuous section of the bundle of germs is continuous, hence
locally constant, on the domain of the chart. -/
private theorem continuousOn_germ (s : C(B, (germBundleCore h B).TotalSpace))
    (hs : (germBundleCore h B).proj ∘ s = id) (e : atlas V B) :
    ContinuousOn (germ s e) e.1.source := by
  have hmaps : MapsTo s e.1.source ((germBundleCore h B).localTriv e).source := fun x hx =>
    ((germBundleCore h B).localTriv e).mem_source.mpr (by
      rw [show (germBundleCore h B).proj (s x) = x from congr_fun hs x,
        ← FiberBundleCore.baseSet_at, germBundleCore_baseSet]
      exact hx)
  exact continuous_snd.comp_continuousOn
    (((germBundleCore h B).localTriv e).continuousOn.comp s.continuous.continuousOn hmaps)

variable (h B) in
/-- A point of the covering space of germs lies over each point of `B`, in the chart at `x`. -/
private theorem mem_source_indexAt (x : B) :
    x ∈ ((germBundleCore h B).indexAt x).1.source := by
  have := (germBundleCore h B).mem_baseSet_at x
  rwa [germBundleCore_baseSet] at this

/-- The developing map of a section `s` of the bundle of germs: at `x`, the inverse of the fibre
coordinate in the chart `e` at `x` applied to the point `e x`. -/
private def devOfSection (s : C(B, (germBundleCore h B).TotalSpace)) (x : B) : V :=
  (germ s ((germBundleCore h B).indexAt x) x)⁻¹ (((germBundleCore h B).indexAt x).1 x)

/-- The developing map of a section is computed in any chart at the point. -/
private theorem devOfSection_eq (s : C(B, (germBundleCore h B).TotalSpace))
    (hs : (germBundleCore h B).proj ∘ s = id) {e : atlas V B} {x : B} (hx : x ∈ e.1.source) :
    devOfSection s x = (germ s e x)⁻¹ (e.1 x) := by
  have hx₀ : x ∈ ((germBundleCore h B).indexAt x).1.source ∩ e.1.source :=
    ⟨mem_source_indexAt h B x, hx⟩
  have hc := chartChange_apply (h := h) hx₀
  rw [devOfSection, germ_change s hs hx₀, mul_inv_rev, IntegralAffineEquiv.mul_apply]
  congr 1
  rw [← hc, ← IntegralAffineEquiv.mul_apply, inv_mul_cancel, IntegralAffineEquiv.one_apply]

/-- The developing map of a continuous section is locally integral affine in every chart: near a
point the fibre coordinate is constant. -/
private theorem isLocallyIntegralAffineOn_devOfSection
    (s : C(B, (germBundleCore h B).TotalSpace)) (hs : (germBundleCore h B).proj ∘ s = id)
    (e : atlas V B) :
    IsLocallyIntegralAffineOn h h (devOfSection s ∘ e.1.symm) e.1.target := by
  rw [isLocallyIntegralAffineOn_iff]
  intro y hy
  have hx : e.1.symm y ∈ e.1.source := e.1.map_target hy
  have hconst := (continuousOn_germ s hs e).continuousAt (e.1.open_source.mem_nhds hx)
  have hnhds : ({germ s e (e.1.symm y)} : Set (IntegralAffineEquiv h h)) ∈
      𝓝 (germ s e (e.1.symm y)) := (isOpen_discrete _).mem_nhds rfl
  obtain ⟨W, hW, hWopen, hxW⟩ := mem_nhds_iff.mp
    ((hconst.eventually_mem hnhds).and (e.1.open_source.mem_nhds hx))
  refine ⟨(germ s e (e.1.symm y))⁻¹, e.1.target ∩ e.1.symm ⁻¹' W,
    e.1.isOpen_inter_preimage_symm hWopen, ⟨hy, hxW⟩, ?_⟩
  rintro y' ⟨hy'₁, -, hy'₂⟩
  obtain ⟨hg, hz⟩ := hW hy'₂
  rw [Function.comp_apply, devOfSection_eq s hs hz, mem_singleton_iff.mp hg, e.1.right_inv hy'₁]

end GermBundle

/-- **Developing maps exist on simply connected integral-affine spaces.** A simply connected
charted space whose chart changes are locally integral affine has a locally integral-affine
developing map. -/
theorem nonempty_of_simplyConnectedSpace [SimplyConnectedSpace B] :
    Nonempty (DevelopingMap h B) := by
  let : TopologicalSpace (IntegralAffineEquiv h h) := ⊥
  have : DiscreteTopology (IntegralAffineEquiv h h) := ⟨rfl⟩
  have : LocallyPathConnectedSpace B := ChartedSpace.locallyPathConnectedSpace V B
  obtain ⟨x₀⟩ := (inferInstance : PathConnectedSpace B).nonempty
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    (isCoveringMap_germBundleCore (B := B) h).existsUnique_continuousMap_lifts
      (ContinuousMap.id B) x₀ ⟨x₀, (1 : IntegralAffineEquiv h h)⟩ rfl
  exact ⟨⟨devOfSection s, isLocallyIntegralAffineOn_devOfSection s (by simpa using hs)⟩⟩

/-- A simply connected charted space whose chart changes are locally integral affine has a
trivialization of its integral tangent lattice, namely the tangent frames of a developing map. -/
theorem nonempty_trivialization_tangent_of_simplyConnectedSpace [SimplyConnectedSpace B] :
    Nonempty ((ExponentSystem.tangent h B).Trivialization N) :=
  (nonempty_of_simplyConnectedSpace h).map DevelopingMap.tangentTrivialization

end DevelopingMap

end Mei.Toric
