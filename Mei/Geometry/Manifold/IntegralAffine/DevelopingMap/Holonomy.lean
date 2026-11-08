/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.DevelopingMap

/-!
# Uniqueness of developing maps and integral-affine holonomy

On a connected charted space `B` whose chart changes are locally integral affine, two developing
maps `dev` and `dev'` differ by a unique global integral affine equivalence:
`dev' = c ∘ dev` for exactly one `c : IntegralAffineEquiv h h`
(`Mei.Toric.DevelopingMap.existsUnique_eq_apply`). The proof compares the local witnesses of the
two maps in a chart, and uses that a developing map is open near each point
(`Mei.Toric.DevelopingMap.image_mem_nhds`), so that the local transitions are determined, hence
locally constant.

This transition `dev.transition dev'` is characterized by `dev' x = dev.transition dev' (dev x)`
(`Mei.Toric.DevelopingMap.transition_eq_iff`), and its lattice part carries the tangent frames of
`dev` to those of `dev'` (`Mei.Toric.DevelopingMap.tangentFrame_eq_trans_latticeEquiv`).

For an atlas self-map `f` of `B`, for instance a deck transformation of a universal cover, the
pullback `dev.comap f` is again a developing map. The *holonomy* `dev.holonomy f` is the
transition from `dev` to `dev ∘ f`, so that `dev (f x) = dev.holonomy f (dev x)`
(`Mei.Toric.DevelopingMap.holonomy_apply`). It is multiplicative in `f`
(`Mei.Toric.DevelopingMap.holonomy_comp`), and its lattice part intertwines the tangent frames
of `dev` at `x` and at `f x`
(`Mei.Toric.DevelopingMap.tangentFrame_chart_eq_trans_holonomy_latticeEquiv`). On the model
space `V`, every integral affine equivalence is a developing map, and the transition between two of
them is the quotient of the equivalences
(`Mei.Toric.DevelopingMap.transition_ofIntegralAffineEquiv`), so every element of the group occurs
as a transition.

This is the equivariance `dev (g x) = h_g (dev x)` of a developing map under deck
transformations, as in Gross–Siebert, *An Invitation to Toric Degenerations*, §2
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §1 (arXiv:1601.07081v4).
-/

public section

open Set Topology Manifold

namespace Mei.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {B : Type*} [TopologicalSpace B] [ChartedSpace V B]

namespace DevelopingMap

/-- A developing map is open near each point: it carries neighborhoods of `x` to neighborhoods
of `dev x`. -/
theorem image_mem_nhds (dev : DevelopingMap h B) {x : B} {s : Set B} (hs : s ∈ 𝓝 x) :
    dev '' s ∈ 𝓝 (dev x) := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev.isLocallyIntegralAffineOn (achart V x)) _
    ((achart V x).1.map_source (mem_chart_source V x))
  set e := (achart V x).1
  have hx : x ∈ e.source := mem_chart_source V x
  have hdev (y : B) (hy : y ∈ e.source) (hyu : e y ∈ u) : dev y = a (e y) := by
    simpa only [Function.comp_apply, e.left_inv hy] using ha ⟨e.map_source hy, hyu⟩
  have ht : e '' (s ∩ e.source) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx (Filter.inter_mem hs (e.open_source.mem_nhds hx))
  have hfun : ⇑a.toContinuousAffineEquiv = ⇑a :=
    funext (IntegralAffineEquiv.toContinuousAffineEquiv_apply a)
  have hopen : a '' (e '' (s ∩ e.source) ∩ u) ∈ 𝓝 (a (e x)) := by
    rw [← hfun]
    exact a.toContinuousAffineEquiv.toHomeomorph.isOpenMap.image_mem_nhds
      (Filter.inter_mem ht (hu.mem_nhds hxu))
  rw [hdev x hx hxu]
  refine Filter.mem_of_superset hopen ?_
  rintro _ ⟨_, ⟨⟨y, hy, rfl⟩, hyu⟩, rfl⟩
  exact ⟨y, hy.1, hdev y hy.2 hyu⟩

/-- Two integral affine equivalences relating the values of two developing maps near a point
are equal. -/
theorem eq_of_eventually_eq_apply {dev dev' : DevelopingMap h B} {x : B}
    {c c' : IntegralAffineEquiv h h} (hc : ∀ᶠ y in 𝓝 x, dev' y = c (dev y))
    (hc' : ∀ᶠ y in 𝓝 x, dev' y = c' (dev y)) : c = c' := by
  obtain ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.mp (dev.image_mem_nhds (hc.and hc'))
  refine IntegralAffineEquiv.eq_of_eqOn_open ht ⟨_, hxt⟩ fun z hz => ?_
  obtain ⟨y, ⟨hy, hy'⟩, rfl⟩ := hts hz
  exact hy.symm.trans hy'

/-- Near each point, two developing maps differ by a global integral affine equivalence. -/
theorem exists_eventually_eq_apply (dev dev' : DevelopingMap h B) (x : B) :
    ∃ c : IntegralAffineEquiv h h, ∀ᶠ y in 𝓝 x, dev' y = c (dev y) := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev.isLocallyIntegralAffineOn (achart V x)) _
    ((achart V x).1.map_source (mem_chart_source V x))
  obtain ⟨b, v, hv, hxv, hb⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev'.isLocallyIntegralAffineOn (achart V x)) _
    ((achart V x).1.map_source (mem_chart_source V x))
  set e := (achart V x).1
  have hx : x ∈ e.source := mem_chart_source V x
  refine ⟨a.symm.trans b, ?_⟩
  filter_upwards [e.open_source.mem_nhds hx,
    (e.continuousAt hx).preimage_mem_nhds ((hu.inter hv).mem_nhds ⟨hxu, hxv⟩)] with y hy hyuv
  have hya := ha ⟨e.map_source hy, hyuv.1⟩
  have hyb := hb ⟨e.map_source hy, hyuv.2⟩
  simp only [Function.comp_apply, e.left_inv hy] at hya hyb
  simp [hya, hyb]

/-- If two developing maps differ by an integral affine equivalence `c`, their tangent frames
differ by its lattice equivalence. -/
theorem tangentFrame_eq_trans_latticeEquiv {dev dev' : DevelopingMap h B}
    {c : IntegralAffineEquiv h h} (hc : ∀ x, dev' x = c (dev x)) (e : atlas V B) (x : B)
    (hx : x ∈ e.1.source) :
    dev'.tangentFrame e x hx = (dev.tangentFrame e x hx).trans c.latticeEquiv := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (dev.isLocallyIntegralAffineOn e) _ (e.1.map_source hx)
  rw [dev.tangentFrame_eq hx hu hxu ha, dev'.tangentFrame_eq hx hu hxu (a := c * a),
    IntegralAffineEquiv.mul_latticeEquiv]
  intro z hz
  have hz' := ha hz
  simp only [Function.comp_apply] at hz' ⊢
  rw [hc, hz', IntegralAffineEquiv.mul_apply]

variable [ConnectedSpace B]

/-- On a connected space, two developing maps differ by a unique global integral affine
equivalence. -/
theorem existsUnique_eq_apply (dev dev' : DevelopingMap h B) :
    ∃! c : IntegralAffineEquiv h h, ∀ x, dev' x = c (dev x) := by
  choose c hc using exists_eventually_eq_apply dev dev'
  have hloc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(hc x).eventually_nhds] with y hy
    exact eq_of_eventually_eq_apply (hc y) hy
  have hconst (x : B) : c x = c (Classical.arbitrary B) :=
    hloc.apply_eq_of_preconnectedSpace _ _
  have h0 (x : B) : dev' x = c (Classical.arbitrary B) (dev x) := by
    rw [← hconst x]
    exact (hc x).self_of_nhds
  exact ⟨c (Classical.arbitrary B), h0, fun c' hc' =>
    eq_of_eventually_eq_apply (x := Classical.arbitrary B)
      (Filter.Eventually.of_forall hc') (Filter.Eventually.of_forall h0)⟩

/-- The integral affine equivalence carrying the values of one developing map to those of
another on a connected space. -/
noncomputable def transition (dev dev' : DevelopingMap h B) : IntegralAffineEquiv h h :=
  (existsUnique_eq_apply dev dev').exists.choose

/-- The transition of two developing maps on a connected space is the unique integral affine
equivalence carrying the values of the first to those of the second. -/
theorem transition_eq_iff {dev dev' : DevelopingMap h B} {c : IntegralAffineEquiv h h} :
    dev.transition dev' = c ↔ ∀ x, dev' x = c (dev x) :=
  ⟨fun hc => hc ▸ (existsUnique_eq_apply dev dev').exists.choose_spec,
    fun hc => (existsUnique_eq_apply dev dev').unique
      (existsUnique_eq_apply dev dev').exists.choose_spec hc⟩

/-- The transition carries the values of the first developing map to those of the second. -/
theorem transition_apply (dev dev' : DevelopingMap h B) (x : B) :
    dev' x = dev.transition dev' (dev x) :=
  transition_eq_iff.mp rfl x

/-- The holonomy of an atlas self-map `f` of a connected space `B` for a developing map `dev`:
the transition from `dev` to its pullback `dev ∘ f`. For a deck transformation `f` of a universal
cover it is the integral affine holonomy. -/
noncomputable def holonomy (dev : DevelopingMap h B) (f : AtlasMap V B B) :
    IntegralAffineEquiv h h :=
  dev.transition (dev.comap f)

/-- The holonomy of an atlas self-map is the unique integral affine equivalence by which the
developing map is equivariant. -/
theorem holonomy_eq_iff {dev : DevelopingMap h B} {f : AtlasMap V B B}
    {c : IntegralAffineEquiv h h} : dev.holonomy f = c ↔ ∀ x, dev (f x) = c (dev x) := by
  simp only [holonomy, transition_eq_iff, comap_apply]

/-- A developing map is equivariant under an atlas self-map of a connected space, with the
holonomy acting on the values. -/
theorem holonomy_apply (dev : DevelopingMap h B) (f : AtlasMap V B B) (x : B) :
    dev (f x) = dev.holonomy f (dev x) :=
  holonomy_eq_iff.mp rfl x

/-- The identity atlas map has trivial holonomy. -/
@[simp]
theorem holonomy_id (dev : DevelopingMap h B) : dev.holonomy (AtlasMap.id V B) = 1 :=
  holonomy_eq_iff.mpr fun x => by
    rw [AtlasMap.coe_id, id_eq, IntegralAffineEquiv.one_apply]

/-- Holonomy is multiplicative: the holonomy of a composite is the product of the holonomies. -/
@[simp]
theorem holonomy_comp (dev : DevelopingMap h B) (f g : AtlasMap V B B) :
    dev.holonomy (g.comp f) = dev.holonomy g * dev.holonomy f :=
  holonomy_eq_iff.mpr fun x => by
    rw [AtlasMap.coe_comp, Function.comp_apply, holonomy_apply dev g, holonomy_apply dev f,
      IntegralAffineEquiv.mul_apply]

/-- The lattice part of the holonomy of `f` carries the tangent frame of a developing map in a
chart `e` at `x` to its tangent frame in the target chart `f.chart e` at `f x`. -/
theorem tangentFrame_chart_eq_trans_holonomy_latticeEquiv (dev : DevelopingMap h B)
    (f : AtlasMap V B B) (e : atlas V B)
    (x : B) (hx : x ∈ e.1.source) :
    dev.tangentFrame (f.chart e) (f x) ((f.mem_source_iff e).mp hx) =
      (dev.tangentFrame e x hx).trans (dev.holonomy f).latticeEquiv := by
  rw [← tangentFrame_comap]
  exact tangentFrame_eq_trans_latticeEquiv (fun y => by
    rw [comap_apply]; exact holonomy_apply dev f y) e x hx

/-- On the model space `V`, an integral affine equivalence is a developing map. -/
def ofIntegralAffineEquiv (a : IntegralAffineEquiv h h) : DevelopingMap h V where
  toFun := a
  isLocallyIntegralAffineOn' e := by
    have he : e.1 = OpenPartialHomeomorph.refl V := chartedSpaceSelf_atlas.mp e.2
    rw [he]
    exact .of_eqOn a fun _ _ => (rfl)

/-- The developing map of an integral affine equivalence is evaluated by that equivalence. -/
@[simp]
theorem ofIntegralAffineEquiv_apply (a : IntegralAffineEquiv h h) (x : V) :
    ofIntegralAffineEquiv a x = a x := (rfl)

/-- On the model space, the transition from the developing map `a` to the developing map `b` is
`b * a⁻¹`, so every element of the group of integral affine equivalences is a transition. -/
theorem transition_ofIntegralAffineEquiv (a b : IntegralAffineEquiv h h) :
    (ofIntegralAffineEquiv a).transition (ofIntegralAffineEquiv b) = b * a⁻¹ :=
  transition_eq_iff.mpr fun x => by simp

end DevelopingMap

end Mei.Toric
