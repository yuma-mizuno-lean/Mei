/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem.Trivialization

/-!
# Developing maps of integral-affine charted spaces

A developing map `dev : Mei.Toric.DevelopingMap h B` of a charted space `B` whose chart changes
are locally integral affine for the lattice `N ⊆ V` is a map `dev : B → V` that is locally
integral affine in every chart: `dev ∘ e⁻¹` is locally integral affine on the target of every
chart `e`. Its integral linear part at `e x` (`DevelopingMap.tangentFrame`) identifies the
integral tangent lattice in the frame of `e` at `x` with `N`. These identifications are locally
constant and intertwine the tangent frame changes (`DevelopingMap.tangentFrame_coordChange`), so
a developing map trivializes the integral tangent lattice
(`DevelopingMap.tangentTrivialization`). A space whose tangent lattice has no trivialization
therefore has no developing map (`DevelopingMap.isEmpty_of_isEmpty_trivialization`); the
focus-focus base is an example (`Mei.FocusFocus.isEmpty_developingMap`).

Developing maps pull back along atlas maps (`DevelopingMap.comap`), with the tangent frames of
the target charts (`DevelopingMap.tangentFrame_comap`). An atlas map `f` whose image lies in
the domain of a chart `e₀` gives the developing map `e₀ ∘ f`
(`DevelopingMap.ofAtlasMap`), whose tangent frames are the tangent frame changes to `e₀`
(`DevelopingMap.tangentFrame_ofAtlasMap`).

On the universal cover of an integral-affine manifold a developing map exists, and the deck
transformations act on it by integral affine holonomy; see Gross–Siebert, *An Invitation to
Toric Degenerations*, §2 (arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §1 (arXiv:1601.07081v4). A developing map of a
simply connected space exists by `Mei.Toric.DevelopingMap.nonempty_of_simplyConnectedSpace`;
neither the universal cover nor the holonomy is constructed here.
-/

public section

open Set Topology Manifold

namespace Mei.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A developing map of a charted space `B` modelled on `V`: a map `B → V` that is locally
integral affine in every chart, that is, `dev ∘ e⁻¹` is locally integral affine on the target
of every chart `e`. -/
structure DevelopingMap (h : TauCeti.Toric.IsIntegralLattice i) (B : Type*)
    [TopologicalSpace B] [ChartedSpace V B] where
  /-- The underlying map. -/
  toFun : B → V
  /-- In every chart, the map is locally integral affine. -/
  isLocallyIntegralAffineOn' (e : atlas V B) :
    IsLocallyIntegralAffineOn h h (toFun ∘ e.1.symm) e.1.target

namespace DevelopingMap

variable {B B' : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [TopologicalSpace B'] [ChartedSpace V B']

instance : FunLike (DevelopingMap h B) B V where
  coe := toFun
  coe_injective dev dev' hdev := by
    rcases dev with ⟨f, _⟩
    rcases dev' with ⟨f', _⟩
    obtain rfl : f = f' := hdev
    rfl

/-- The underlying map of a developing map is its coercion to a function. -/
@[simp]
theorem toFun_eq_coe (dev : DevelopingMap h B) : dev.toFun = ⇑dev := (rfl)

/-- Two developing maps are equal when their underlying maps agree. -/
@[ext]
theorem ext {dev dev' : DevelopingMap h B} (H : ∀ x, dev x = dev' x) : dev = dev' :=
  DFunLike.ext _ _ H

/-- In every chart `e`, a developing map composed with `e⁻¹` is locally integral affine on the
target of `e`. -/
theorem isLocallyIntegralAffineOn (dev : DevelopingMap h B) (e : atlas V B) :
    IsLocallyIntegralAffineOn h h (dev ∘ e.1.symm) e.1.target :=
  dev.isLocallyIntegralAffineOn' e

/-- The pullback of a developing map along an atlas map: its composite with the atlas map. -/
def comap (dev : DevelopingMap h B) (f : AtlasMap V B' B) : DevelopingMap h B' where
  toFun := dev ∘ f
  isLocallyIntegralAffineOn' e := by
    refine ((dev.isLocallyIntegralAffineOn (f.chart e)).mono
      (f.target_subset_chart_target e)).congr fun y hy => ?_
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
      f.apply_symm_eq_chart_symm e hy]

/-- The pullback of a developing map along an atlas map is evaluated at the image point. -/
@[simp]
theorem comap_apply (dev : DevelopingMap h B) (f : AtlasMap V B' B) (x : B') :
    dev.comap f x = dev (f x) := (rfl)

/-- The tangent frame of a developing map in the chart `e` at a point `x` of its domain: the
integral linear part of `dev ∘ e⁻¹` at `e x`. -/
noncomputable def tangentFrame (dev : DevelopingMap h B) (e : atlas V B) (x : B)
    (hx : x ∈ e.1.source) : N ≃+ N :=
  (dev.isLocallyIntegralAffineOn e).latticeEquivAt (e.1.map_source hx)

/-- The tangent frame of a developing map in the chart `e` at `x` is the lattice equivalence of
every integral affine equivalence agreeing with `dev ∘ e⁻¹` near `e x`. -/
theorem tangentFrame_eq (dev : DevelopingMap h B) {e : atlas V B} {x : B}
    (hx : x ∈ e.1.source) {a : IntegralAffineEquiv h h} {u : Set V} (hu : IsOpen u)
    (hxu : e.1 x ∈ u) (ha : EqOn (dev ∘ e.1.symm) a (e.1.target ∩ u)) :
    dev.tangentFrame e x hx = a.latticeEquiv :=
  (dev.isLocallyIntegralAffineOn e).latticeEquivAt_eq e.1.open_target _ hu hxu ha

/-- The tangent frame of the pullback of a developing map along an atlas map, in a chart at a
point, is the tangent frame of the developing map in the target chart at the image point. -/
theorem tangentFrame_comap (dev : DevelopingMap h B) (f : AtlasMap V B' B) (e : atlas V B')
    (x : B') (hx : x ∈ e.1.source) :
    (dev.comap f).tangentFrame e x hx =
      dev.tangentFrame (f.chart e) (f x) ((f.mem_source_iff e).mp hx) := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev.isLocallyIntegralAffineOn (f.chart e)) _
    ((f.chart e).1.map_source ((f.mem_source_iff e).mp hx))
  rw [dev.tangentFrame_eq _ hu hxu ha]
  rw [f.chart_apply e hx] at hxu
  refine tangentFrame_eq _ hx hu hxu fun y hy => ?_
  rw [← ha ⟨f.target_subset_chart_target e hy.1, hy.2⟩, Function.comp_apply, comap_apply,
    Function.comp_apply, f.apply_symm_eq_chart_symm e hy.1]

/-- The tangent frames of a developing map are locally constant on the domain of each
chart. -/
theorem eventually_tangentFrame_eq (dev : DevelopingMap h B) {e : atlas V B} {x : B}
    (hx : x ∈ e.1.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.1.source, dev.tangentFrame e y hy = dev.tangentFrame e x hx := by
  filter_upwards [(e.1.continuousAt hx).eventually
    ((dev.isLocallyIntegralAffineOn e).eventually_latticeEquivAt_eq e.1.open_target
      (e.1.map_source hx))] with y hy hy'
  exact hy _

variable [HasGroupoid B (integralAffineGroupoid h)]

/-- On the overlap of two charts, the tangent frame change followed by the tangent frame of a
developing map in the second chart is its tangent frame in the first chart. -/
theorem tangentFrame_coordChange (dev : DevelopingMap h B) {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    (tangentLatticeChange h e e' x).trans (dev.tangentFrame e' x hx.2) =
      dev.tangentFrame e x hx.1 := by
  obtain ⟨a, u, hu, hxu, ha, hT⟩ := exists_tangentLatticeChange_eq (h := h) hx
  obtain ⟨b, v, hv, hxv, hb⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev.isLocallyIntegralAffineOn e') (e'.1 x) (e'.1.map_source hx.2)
  have hex : e.1.symm (e.1 x) = x := e.1.left_inv hx.1
  have hax : a (e.1 x) = e'.1 x := (ha ⟨PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv
    hx.1 hx.2, hxu⟩).symm.trans (congrArg e'.1 hex)
  have hO : IsOpen (u ∩ a ⁻¹' v ∩ (e.1.symm ≫ₕ e'.1).source) :=
    (hu.inter (hv.preimage a.continuous)).inter (e.1.symm ≫ₕ e'.1).open_source
  have hxO : e.1 x ∈ u ∩ a ⁻¹' v ∩ (e.1.symm ≫ₕ e'.1).source :=
    ⟨⟨hxu, by rwa [mem_preimage, hax]⟩,
      PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2⟩
  rw [hT, dev.tangentFrame_eq hx.2 hv hxv hb, dev.tangentFrame_eq hx.1 hO hxO (a := a.trans b),
    IntegralAffineEquiv.trans_latticeEquiv]
  rintro y ⟨-, ⟨hyu, hyv⟩, hy⟩
  have hy' : e.1.symm y ∈ e'.1.source := hy.2
  have hay : e'.1 (e.1.symm y) = a y := ha ⟨hy, hyu⟩
  have hby := hb ⟨e'.1.map_source hy', by rwa [mem_preimage, ← hay] at hyv⟩
  rw [Function.comp_apply, e'.1.left_inv hy', hay] at hby
  rw [Function.comp_apply, hby, IntegralAffineEquiv.trans_toAffineEquiv, AffineEquiv.trans_apply]

/-- The trivialization of the integral tangent lattice by the tangent frames of a developing
map. -/
noncomputable def tangentTrivialization (dev : DevelopingMap h B) :
    (ExponentSystem.tangent h B).Trivialization N where
  frame := dev.tangentFrame
  frame_coordChange hx n := by
    rw [ExponentSystem.tangent_coordChange, ← AddEquiv.trans_apply,
      dev.tangentFrame_coordChange hx]
  eventually_frame_eq := dev.eventually_tangentFrame_eq

/-- The frames of the tangent trivialization of a developing map are its tangent frames. -/
@[simp]
theorem tangentTrivialization_frame (dev : DevelopingMap h B) (e : atlas V B) (x : B)
    (hx : x ∈ e.1.source) : dev.tangentTrivialization.frame e x hx = dev.tangentFrame e x hx :=
  (rfl)

/-- If the integral tangent lattice of `B` has no trivialization, then `B` has no developing
map. -/
theorem isEmpty_of_isEmpty_trivialization
    (hB : IsEmpty ((ExponentSystem.tangent h B).Trivialization N)) :
    IsEmpty (DevelopingMap h B) :=
  ⟨fun dev => hB.false dev.tangentTrivialization⟩

/-- Let `f` be an atlas map whose image lies in the domain of the chart `e₀`. Then the chart
`e₀` composed with `f` is a developing map. -/
def ofAtlasMap (f : AtlasMap V B' B) (e₀ : atlas V B) (hf : ∀ x, f x ∈ e₀.1.source) :
    DevelopingMap h B' where
  toFun := e₀.1 ∘ f
  isLocallyIntegralAffineOn' e := by
    refine ((isLocallyIntegralAffineOn_symm_trans h (f.chart e) e₀).mono fun y hy => ?_).congr
      fun y hy => ?_
    · refine ⟨f.target_subset_chart_target e hy, show (f.chart e).1.symm y ∈ e₀.1.source from ?_⟩
      rw [← f.apply_symm_eq_chart_symm e hy]
      exact hf _
    · rw [OpenPartialHomeomorph.trans_apply, Function.comp_apply, Function.comp_apply,
        f.apply_symm_eq_chart_symm e hy]

/-- The developing map given by a chart `e₀` along an atlas map `f` is `e₀ ∘ f`. -/
@[simp]
theorem ofAtlasMap_apply (f : AtlasMap V B' B) (e₀ : atlas V B) (hf : ∀ x, f x ∈ e₀.1.source)
    (x : B') : ofAtlasMap (h := h) f e₀ hf x = e₀.1 (f x) := (rfl)

/-- The tangent frame of the developing map `e₀ ∘ f` in a chart `e` at `x` is the tangent frame
change from the target chart of `e` to `e₀` at `f x`. -/
theorem tangentFrame_ofAtlasMap (f : AtlasMap V B' B) (e₀ : atlas V B)
    (hf : ∀ x, f x ∈ e₀.1.source) (e : atlas V B') (x : B') (hx : x ∈ e.1.source) :
    (ofAtlasMap (h := h) f e₀ hf).tangentFrame e x hx =
      tangentLatticeChange h (f.chart e) e₀ (f x) := by
  obtain ⟨a, u, hu, hxu, ha, hT⟩ :=
    exists_tangentLatticeChange_eq (h := h) ⟨(f.mem_source_iff e).mp hx, hf x⟩
  rw [f.chart_apply e hx] at hxu
  refine (tangentFrame_eq _ hx hu hxu fun y hy => ?_).trans hT.symm
  have hy₀ : (f.chart e).1.symm y ∈ e₀.1.source := by
    rw [← f.apply_symm_eq_chart_symm e hy.1]
    exact hf _
  have hys : y ∈ ((f.chart e).1.symm ≫ₕ e₀.1).source :=
    ⟨f.target_subset_chart_target e hy.1, hy₀⟩
  rw [← ha ⟨hys, hy.2⟩, OpenPartialHomeomorph.trans_apply, Function.comp_apply,
    ofAtlasMap_apply, f.apply_symm_eq_chart_symm e hy.1]

end DevelopingMap

end Mei.Toric
