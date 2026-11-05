/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem.Iso

/-!
# Trivializations of exponent systems

A trivialization `τ : E.Trivialization Γ₀` of an exponent system `E` with fibre `Γ` on an
integral-affine charted space `B` (`Mei.Toric.ExponentSystem.Trivialization`) is a global frame
of its lattice local system with model fibre `Γ₀`: in the frame of each chart `e` and at each
point `x` of its domain, a lattice isomorphism `τ_e(x) : Γ ≃ Γ₀`, locally constant in `x`, with
`τ_{e'}(x) ∘ T_Γ = τ_e(x)` on overlaps. The projections to the tangent lattice play no role.

A trivialization determines the frame changes on overlaps (`Trivialization.coordChange_eq`), and
its frames are constant on preconnected subsets of chart domains
(`Trivialization.frame_eq_of_isPreconnected`). Hence the existence of a trivialization forces
the frame change between two charts to take the same value at two points that are joined by
preconnected subsets of both chart domains (`Trivialization.coordChange_eq_of_isPreconnected`).
This is the obstruction coming from monodromy: when the frame change takes different values at
two such points, there is no trivialization.

Trivializations pull back along atlas maps (`Trivialization.comap`) and along isomorphisms of
exponent systems (`Trivialization.ofIso`). The pullback of an exponent system along an atlas
map whose image lies in the domain of a single chart `e₀` is trivialized by the frame changes
to `e₀` (`Trivialization.ofAtlasMap`). Trivializations of the tangent exponent system come
from developing maps (`Mei.Toric.DevelopingMap.tangentTrivialization`). The focus-focus
exponent system has no trivialization, while its restriction to the upper half-plane has one
(`Mei.FocusFocus.isEmpty_exponentSystem_trivialization`,
`Mei.FocusFocus.upperHalfPlaneTrivialization`).

Trivializations of the lattice local systems lifted to the universal cover of an
integral-affine manifold appear in Gross–Siebert, *An Invitation to Toric Degenerations*, §2
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §§1 and 3 (arXiv:1601.07081v4).
-/

public section

open Set Topology Manifold

namespace Mei.Toric.ExponentSystem

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {B B' : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [HasGroupoid B (integralAffineGroupoid h)]
  [TopologicalSpace B'] [ChartedSpace V B'] [HasGroupoid B' (integralAffineGroupoid h)]
  {Γ Γ' : Type*} [AddCommGroup Γ] [AddCommGroup Γ']

/-- A trivialization of an exponent system `E` with model fibre `Γ₀`: in the frame of each
chart and at each point of its domain, a lattice isomorphism from the fibre of `E` to `Γ₀`,
locally constant in the point, such that on overlaps the frame change of `E` followed by the
isomorphism of the second chart is the isomorphism of the first chart. -/
structure Trivialization (E : ExponentSystem h B Γ) (Γ₀ : Type*) [AddCommGroup Γ₀] where
  /-- The isomorphism to the model fibre in the frame of a chart at a point of its domain. -/
  frame (e : atlas V B) (x : B) : x ∈ e.1.source → Γ ≃+ Γ₀
  /-- On overlaps, the frames are compatible with the frame changes. -/
  frame_coordChange {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) (γ : Γ) :
    frame e' x hx.2 (E.coordChange e e' x γ) = frame e x hx.1 γ
  /-- The frames are locally constant on the domain of each chart. -/
  eventually_frame_eq {e : atlas V B} {x : B} (hx : x ∈ e.1.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.1.source, frame e y hy = frame e x hx

namespace Trivialization

variable {Γ₀ : Type*} [AddCommGroup Γ₀] {E : ExponentSystem h B Γ} {E' : ExponentSystem h B Γ'}

/-- Two trivializations are equal when their frames agree. -/
@[ext]
theorem ext {τ τ' : E.Trivialization Γ₀}
    (H : ∀ e x (hx : x ∈ e.1.source) γ, τ.frame e x hx γ = τ'.frame e x hx γ) : τ = τ' := by
  rcases τ with ⟨τ, _, _⟩
  rcases τ' with ⟨τ', _, _⟩
  obtain rfl : τ = τ' := by
    funext e x hx
    exact AddEquiv.ext (H e x hx)
  rfl

/-- On overlaps, a trivialization determines the frame change: it is the frame of the first
chart followed by the inverse frame of the second. -/
theorem coordChange_eq (τ : E.Trivialization Γ₀) {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    E.coordChange e e' x = (τ.frame e x hx.1).trans (τ.frame e' x hx.2).symm := by
  ext γ
  rw [AddEquiv.trans_apply, AddEquiv.eq_symm_apply, τ.frame_coordChange hx]

/-- The frame of a trivialization in a chart is constant on every preconnected subset of the
domain of the chart. -/
theorem frame_eq_of_isPreconnected (τ : E.Trivialization Γ₀) {e : atlas V B} {s : Set B}
    (hs : IsPreconnected s) (hse : s ⊆ e.1.source) {x y : B} (hx : x ∈ s) (hy : y ∈ s) :
    τ.frame e x (hse hx) = τ.frame e y (hse hy) := by
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  have hc : IsLocallyConstant fun z : s => τ.frame e z (hse z.2) := by
    refine IsLocallyConstant.iff_eventually_eq _ |>.mpr fun z => ?_
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (τ.eventually_frame_eq (hse z.2))] with w hw
    exact hw _
  exact hc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- If an exponent system has a trivialization, then its frame change between two charts takes
the same value at any two points lying both in a preconnected subset `s` of the domain of the
first chart and in a preconnected subset `s'` of the domain of the second chart. -/
theorem coordChange_eq_of_isPreconnected (τ : E.Trivialization Γ₀) {e e' : atlas V B}
    {s s' : Set B} (hs : IsPreconnected s) (hs' : IsPreconnected s') (hse : s ⊆ e.1.source)
    (hse' : s' ⊆ e'.1.source) {x y : B} (hx : x ∈ s ∩ s') (hy : y ∈ s ∩ s') :
    E.coordChange e e' x = E.coordChange e e' y := by
  rw [τ.coordChange_eq ⟨hse hx.1, hse' hx.2⟩, τ.coordChange_eq ⟨hse hy.1, hse' hy.2⟩,
    τ.frame_eq_of_isPreconnected hs hse hx.1 hy.1,
    τ.frame_eq_of_isPreconnected hs' hse' hx.2 hy.2]

/-- The pullback of a trivialization along an atlas map: its frame in a chart at a point is the
frame in the target chart at the image point. -/
def comap (τ : E.Trivialization Γ₀) (f : AtlasMap V B' B) : (E.comap f).Trivialization Γ₀ where
  frame e x hx := τ.frame (f.chart e) (f x) ((f.mem_source_iff e).mp hx)
  frame_coordChange {e e' x} hx γ := by
    rw [comap_coordChange]
    exact τ.frame_coordChange ((f.mem_source_inter_iff e e').mp hx) γ
  eventually_frame_eq {e x} hx := by
    filter_upwards [f.continuous.continuousAt.eventually
      (τ.eventually_frame_eq ((f.mem_source_iff e).mp hx))] with y hy hy'
    exact hy _

/-- The frame of a pulled-back trivialization in a chart is the frame in its target chart at
the image point. -/
@[simp]
theorem comap_frame (τ : E.Trivialization Γ₀) (f : AtlasMap V B' B) (e : atlas V B') (x : B')
    (hx : x ∈ e.1.source) :
    (τ.comap f).frame e x hx = τ.frame (f.chart e) (f x) ((f.mem_source_iff e).mp hx) := (rfl)

/-- The pullback of a trivialization along an isomorphism of exponent systems: its frame is the
component of the isomorphism followed by the frame of the trivialization. -/
def ofIso (σ : E.Iso E') (τ : E'.Trivialization Γ₀) : E.Trivialization Γ₀ where
  frame e x hx := (σ.app e x hx).trans (τ.frame e x hx)
  frame_coordChange hx γ := by
    rw [AddEquiv.trans_apply, AddEquiv.trans_apply, σ.app_coordChange hx,
      τ.frame_coordChange hx]
  eventually_frame_eq {e x} hx := by
    filter_upwards [σ.eventually_app_eq hx, τ.eventually_frame_eq hx] with y hσ hτ hy
    rw [hσ hy, hτ hy]

/-- The frame of the pullback of a trivialization along an isomorphism is the component of the
isomorphism followed by the frame of the trivialization. -/
@[simp]
theorem ofIso_frame (σ : E.Iso E') (τ : E'.Trivialization Γ₀) (e : atlas V B) (x : B)
    (hx : x ∈ e.1.source) :
    (ofIso σ τ).frame e x hx = (σ.app e x hx).trans (τ.frame e x hx) := (rfl)

variable (E) in
/-- Let `f` be an atlas map whose image lies in the domain of the chart `e₀`. The pullback
`E.comap f` of an exponent system `E` is trivialized, with model fibre `Γ`, by the frame changes
of `E` to `e₀`: the frame in a chart `e` at `x` is `E.coordChange (f.chart e) e₀ (f x)`. -/
def ofAtlasMap (f : AtlasMap V B' B) (e₀ : atlas V B) (hf : ∀ x, f x ∈ e₀.1.source) :
    (E.comap f).Trivialization Γ where
  frame e x _ := E.coordChange (f.chart e) e₀ (f x)
  frame_coordChange {e e' x} hx γ := by
    rw [comap_coordChange, ← AddEquiv.trans_apply,
      E.coordChange_trans ⟨(f.mem_source_inter_iff e e').mp hx, hf x⟩]
  eventually_frame_eq {e x} hx := by
    filter_upwards [f.continuous.continuousAt.eventually
      (E.eventually_coordChange_eq ⟨(f.mem_source_iff e).mp hx, hf x⟩)] with y hy _
    exact hy

/-- The frame of the trivialization by the frame changes to a chart `e₀` is, in a chart `e` at
`x`, the frame change from the target chart of `e` to `e₀` at `f x`. -/
@[simp]
theorem ofAtlasMap_frame (f : AtlasMap V B' B) (e₀ : atlas V B) (hf : ∀ x, f x ∈ e₀.1.source)
    (e : atlas V B') (x : B') (hx : x ∈ e.1.source) :
    (ofAtlasMap E f e₀ hf).frame e x hx = E.coordChange (f.chart e) e₀ (f x) := (rfl)

end Trivialization

end Mei.Toric.ExponentSystem
