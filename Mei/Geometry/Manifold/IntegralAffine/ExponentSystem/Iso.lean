/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.Pullback

/-!
# Isomorphisms of exponent systems

An isomorphism `σ : E.Iso E'` of exponent systems on the same integral-affine charted space `B`
(`Mei.Toric.ExponentSystem.Iso`) is an isomorphism of the underlying lattice local systems
over the identity of the tangent lattice: in the frame of each chart `e` and at each point `x`
of its domain, a lattice isomorphism `σ_e(x) : Γ ≃ Γ'`, locally constant in `x`, intertwining
the frame changes of `E` and `E'` on overlaps and satisfying `ρ'_e ∘ σ_e(x) = ρ_e`.

Isomorphisms form a groupoid (`Iso.refl`, `Iso.symm`, `Iso.trans`), and the automorphisms of an
exponent system form a group. A single lattice isomorphism commuting with all frame changes
and projections is an isomorphism with constant components (`Iso.ofAddEquiv`).

Isomorphisms pull back along atlas maps (`Iso.comap`), compatibly with identities, inverses and
composites. The pullback of an exponent system along an atlas map depends on the choice of the
target charts only up to a canonical isomorphism: for two atlas maps `f` and `g` with the same
underlying map, `ExponentSystem.comapCongr` is the isomorphism from `E.comap f` to `E.comap g`
whose component in the frame of a chart `e` at `x` is the frame change of `E` from `f.chart e`
to `g.chart e` at `f x`. These isomorphisms are identities for `f = g`, compose, invert, and are
natural in `E`. In particular the restriction of an exponent system to an open subset, along
any atlas map whose underlying map is the inclusion, is canonically isomorphic to the
restriction along `Mei.AtlasMap.ofOpens`.

Isomorphisms of lattice local systems over integral-affine manifolds compatible with the map
to the tangent lattice appear in Gross–Siebert, *An Invitation to Toric Degenerations*, §2
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
  {Γ Γ' Γ'' Γ''' : Type*} [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommGroup Γ''']

/-- An isomorphism of exponent systems on the same integral-affine charted space: in the frame
of each chart and at each point of its domain, a lattice isomorphism of the fibres, locally
constant in the point, intertwining the frame changes on overlaps and compatible with the
projections to the integral tangent lattice. -/
structure Iso (E : ExponentSystem h B Γ) (E' : ExponentSystem h B Γ') where
  /-- The component in the frame of a chart at a point of its domain. -/
  app (e : atlas V B) (x : B) : x ∈ e.val.source → Γ ≃+ Γ'
  /-- On overlaps, the components intertwine the frame changes. -/
  app_coordChange {e e' : atlas V B} {x : B} (hx : x ∈ e.val.source ∩ e'.val.source) (γ : Γ) :
    app e' x hx.2 (E.coordChange e e' x γ) = E'.coordChange e e' x (app e x hx.1 γ)
  /-- The components are locally constant on the domain of each chart. -/
  eventually_app_eq {e : atlas V B} {x : B} (hx : x ∈ e.val.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.val.source, app e y hy = app e x hx
  /-- The components are compatible with the projections: `ρ'_e ∘ σ_e(x) = ρ_e`. -/
  projection_app {e : atlas V B} {x : B} (hx : x ∈ e.val.source) (γ : Γ) :
    E'.projection e (app e x hx γ) = E.projection e γ

namespace Iso

variable {E : ExponentSystem h B Γ} {E' : ExponentSystem h B Γ'}
  {E'' : ExponentSystem h B Γ''} {E''' : ExponentSystem h B Γ'''}

/-- Two isomorphisms of exponent systems are equal when their components agree. -/
@[ext]
theorem ext {σ τ : E.Iso E'}
    (hστ : ∀ e x (hx : x ∈ e.val.source) γ, σ.app e x hx γ = τ.app e x hx γ) : σ = τ := by
  rcases σ with ⟨σ, _, _, _⟩
  rcases τ with ⟨τ, _, _, _⟩
  obtain rfl : σ = τ := by
    funext e x hx
    exact AddEquiv.ext (hστ e x hx)
  rfl

variable (E) in
/-- The identity isomorphism of an exponent system. -/
def refl : E.Iso E where
  app _ _ _ := AddEquiv.refl Γ
  app_coordChange _ _ := by rw [AddEquiv.refl_apply, AddEquiv.refl_apply]
  eventually_app_eq _ := Filter.Eventually.of_forall fun _ _ => rfl
  projection_app _ _ := by rw [AddEquiv.refl_apply]

/-- The components of the identity isomorphism are identities. -/
@[simp]
theorem refl_app (e : atlas V B) (x : B) (hx : x ∈ e.val.source) :
    (refl E).app e x hx = AddEquiv.refl Γ := (rfl)

/-- The inverse of an isomorphism of exponent systems. -/
def symm (σ : E.Iso E') : E'.Iso E where
  app e x hx := (σ.app e x hx).symm
  app_coordChange {e e' x} hx γ := (σ.app e' x hx.2).injective <| by
    rw [AddEquiv.apply_symm_apply, σ.app_coordChange hx, AddEquiv.apply_symm_apply]
  eventually_app_eq {e x} hx := by
    filter_upwards [σ.eventually_app_eq hx] with y hy hy'
    rw [hy hy']
  projection_app {e x} hx γ := by
    rw [← σ.projection_app hx, AddEquiv.apply_symm_apply]

/-- The components of the inverse isomorphism are the inverse components. -/
@[simp]
theorem symm_app (σ : E.Iso E') (e : atlas V B) (x : B) (hx : x ∈ e.val.source) :
    σ.symm.app e x hx = (σ.app e x hx).symm := (rfl)

/-- The composite of two isomorphisms of exponent systems. -/
def trans (σ : E.Iso E') (τ : E'.Iso E'') : E.Iso E'' where
  app e x hx := (σ.app e x hx).trans (τ.app e x hx)
  app_coordChange {e e' x} hx γ := by
    rw [AddEquiv.trans_apply, AddEquiv.trans_apply, σ.app_coordChange hx, τ.app_coordChange hx]
  eventually_app_eq {e x} hx := by
    filter_upwards [σ.eventually_app_eq hx, τ.eventually_app_eq hx] with y hσ hτ hy
    rw [hσ hy, hτ hy]
  projection_app {e x} hx γ := by
    rw [AddEquiv.trans_apply, τ.projection_app hx, σ.projection_app hx]

/-- The components of a composite are the composites of the components. -/
@[simp]
theorem trans_app (σ : E.Iso E') (τ : E'.Iso E'') (e : atlas V B) (x : B)
    (hx : x ∈ e.val.source) : (σ.trans τ).app e x hx = (σ.app e x hx).trans (τ.app e x hx) :=
  (rfl)

/-- Composing with the identity on the left does nothing. -/
@[simp]
theorem refl_trans (σ : E.Iso E') : (refl E).trans σ = σ := by
  ext
  simp

/-- Composing with the identity on the right does nothing. -/
@[simp]
theorem trans_refl (σ : E.Iso E') : σ.trans (refl E') = σ := by
  ext
  simp

/-- Inverting twice does nothing. -/
@[simp]
theorem symm_symm (σ : E.Iso E') : σ.symm.symm = σ := by
  ext
  simp

/-- The inverse of the identity is the identity. -/
@[simp]
theorem symm_refl : (refl E).symm = refl E := by
  ext
  simp

/-- An isomorphism followed by its inverse is the identity. -/
@[simp]
theorem self_trans_symm (σ : E.Iso E') : σ.trans σ.symm = refl E := by
  ext
  simp

/-- The inverse of an isomorphism followed by the isomorphism is the identity. -/
@[simp]
theorem symm_trans_self (σ : E.Iso E') : σ.symm.trans σ = refl E' := by
  ext
  simp

/-- Composition of isomorphisms of exponent systems is associative. -/
theorem trans_assoc (σ : E.Iso E') (τ : E'.Iso E'') (υ : E''.Iso E''') :
    (σ.trans τ).trans υ = σ.trans (τ.trans υ) := by
  ext
  simp

/-- The inverse of a composite is the composite of the inverses in the opposite order. -/
theorem symm_trans (σ : E.Iso E') (τ : E'.Iso E'') :
    (σ.trans τ).symm = τ.symm.trans σ.symm := by
  ext
  simp

/-- The automorphisms of an exponent system form a group, with multiplication `σ * τ` the
composite applying `τ` first. -/
instance : Group (E.Iso E) where
  mul σ τ := τ.trans σ
  one := refl E
  inv := symm
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/-- The product of two automorphisms applies the right factor first. -/
theorem mul_def (σ τ : E.Iso E) : σ * τ = τ.trans σ := (rfl)

/-- The unit automorphism is the identity. -/
theorem one_def : (1 : E.Iso E) = refl E := (rfl)

/-- The inverse automorphism is the inverse isomorphism. -/
theorem inv_def (σ : E.Iso E) : σ⁻¹ = σ.symm := (rfl)

/-- A lattice isomorphism of the fibres commuting with all frame changes on overlaps and with
all projections, as an isomorphism of exponent systems with constant components. -/
def ofAddEquiv (σ : Γ ≃+ Γ')
    (hc : ∀ (e e' : atlas V B) (x : B), x ∈ e.val.source ∩ e'.val.source → ∀ γ : Γ,
      σ (E.coordChange e e' x γ) = E'.coordChange e e' x (σ γ))
    (hp : ∀ (e : atlas V B) (γ : Γ), E'.projection e (σ γ) = E.projection e γ) : E.Iso E' where
  app _ _ _ := σ
  app_coordChange hx γ := hc _ _ _ hx γ
  eventually_app_eq _ := Filter.Eventually.of_forall fun _ _ => rfl
  projection_app _ γ := hp _ γ

/-- Every component of the isomorphism with constant components is the given lattice
isomorphism. -/
@[simp]
theorem ofAddEquiv_app (σ : Γ ≃+ Γ')
    (hc : ∀ (e e' : atlas V B) (x : B), x ∈ e.val.source ∩ e'.val.source → ∀ γ : Γ,
      σ (E.coordChange e e' x γ) = E'.coordChange e e' x (σ γ))
    (hp : ∀ (e : atlas V B) (γ : Γ), E'.projection e (σ γ) = E.projection e γ)
    (e : atlas V B) (x : B) (hx : x ∈ e.val.source) : (ofAddEquiv σ hc hp).app e x hx = σ := (rfl)

section comap

/-- The pullback of an isomorphism of exponent systems along an atlas map: its component in
the frame of a chart at a point is the component in the frame of the target chart at the
image point. -/
def comap (σ : E.Iso E') (f : AtlasMap V B' B) : (E.comap f).Iso (E'.comap f) where
  app e x hx := σ.app (f.chart e) (f x) ((f.mem_source_iff e).mp hx)
  app_coordChange {e e' x} hx γ := by
    rw [comap_coordChange, comap_coordChange]
    exact σ.app_coordChange ((f.mem_source_inter_iff e e').mp hx) γ
  eventually_app_eq {e x} hx := by
    filter_upwards [f.continuous.continuousAt.eventually
      (σ.eventually_app_eq ((f.mem_source_iff e).mp hx))] with y hy hy'
    exact hy _
  projection_app {e x} hx γ := by
    rw [comap_projection, comap_projection]
    exact σ.projection_app _ γ

/-- The component of a pulled-back isomorphism in a chart is the component in its target chart
at the image point. -/
@[simp]
theorem comap_app (σ : E.Iso E') (f : AtlasMap V B' B) (e : atlas V B') (x : B')
    (hx : x ∈ e.val.source) :
    (σ.comap f).app e x hx = σ.app (f.chart e) (f x) ((f.mem_source_iff e).mp hx) := (rfl)

/-- The pullback of the identity isomorphism is the identity. -/
@[simp]
theorem comap_refl (f : AtlasMap V B' B) : (refl E).comap f = refl (E.comap f) := by
  ext
  simp

/-- Pullback commutes with inverses. -/
@[simp]
theorem comap_symm (σ : E.Iso E') (f : AtlasMap V B' B) : σ.symm.comap f = (σ.comap f).symm := by
  ext
  simp

/-- Pullback commutes with composites. -/
@[simp]
theorem comap_trans (σ : E.Iso E') (τ : E'.Iso E'') (f : AtlasMap V B' B) :
    (σ.trans τ).comap f = (σ.comap f).trans (τ.comap f) := by
  ext
  simp

end comap

end Iso

section comapCongr

variable (E : ExponentSystem h B Γ)

/-- For two atlas maps `f` and `g` with the same underlying map, the canonical isomorphism
between the pullbacks of an exponent system along them: its component in the frame of a chart
`e` at `x` is the frame change from `f.chart e` to `g.chart e` at `f x`. -/
def comapCongr (f g : AtlasMap V B' B) (hfg : ⇑f = ⇑g) : (E.comap f).Iso (E.comap g) where
  app e x _ := E.coordChange (f.chart e) (g.chart e) (f x)
  app_coordChange {e e' x} hx γ := by
    have h₁ := AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx.1
    have h₂ := AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx.2
    rw [comap_coordChange, comap_coordChange, ← AddEquiv.trans_apply,
      E.coordChange_trans ⟨⟨h₁.1, h₂.1⟩, h₂.2⟩, ← AddEquiv.trans_apply, ← congrFun hfg x,
      E.coordChange_trans ⟨⟨h₁.1, h₁.2⟩, h₂.2⟩]
  eventually_app_eq {e x} hx := by
    filter_upwards [f.continuous.continuousAt.eventually
      (E.eventually_coordChange_eq (AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx))]
      with y hy _
    exact hy
  projection_app {e x} hx γ := by
    rw [comap_projection, comap_projection,
      E.projection_coordChange (AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx),
      f.tangentLatticeChange_chart_chart_of_coe_eq g hfg e hx, AddEquiv.refl_apply]

/-- The component of the canonical isomorphism between pullbacks in the frame of a chart `e` at
`x` is the frame change from `f.chart e` to `g.chart e` at `f x`. -/
@[simp]
theorem comapCongr_app (f g : AtlasMap V B' B) (hfg : ⇑f = ⇑g) (e : atlas V B') (x : B')
    (hx : x ∈ e.val.source) :
    (E.comapCongr f g hfg).app e x hx = E.coordChange (f.chart e) (g.chart e) (f x) := (rfl)

/-- The canonical isomorphism between the pullbacks along the same atlas map is the
identity. -/
@[simp]
theorem comapCongr_self (f : AtlasMap V B' B) : E.comapCongr f f rfl = Iso.refl _ := by
  ext e x hx γ
  rw [comapCongr_app, E.coordChange_self ((f.mem_source_iff e).mp hx), Iso.refl_app]

/-- The canonical isomorphisms between pullbacks compose. -/
@[simp]
theorem comapCongr_trans (f g k : AtlasMap V B' B) (hfg : ⇑f = ⇑g) (hgk : ⇑g = ⇑k) :
    (E.comapCongr f g hfg).trans (E.comapCongr g k hgk) = E.comapCongr f k (hfg.trans hgk) := by
  ext e x hx γ
  have h₁ := AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx
  have h₂ := AtlasMap.mem_chart_source_inter_of_coe_eq (hfg.trans hgk) hx
  rw [Iso.trans_app, comapCongr_app, comapCongr_app, comapCongr_app, ← congrFun hfg x,
    E.coordChange_trans ⟨h₁, h₂.2⟩]

/-- The inverse of the canonical isomorphism between pullbacks is the canonical isomorphism in
the opposite direction. -/
@[simp]
theorem comapCongr_symm (f g : AtlasMap V B' B) (hfg : ⇑f = ⇑g) :
    (E.comapCongr f g hfg).symm = E.comapCongr g f hfg.symm := by
  ext e x hx γ
  rw [Iso.symm_app, comapCongr_app, comapCongr_app, ← congrFun hfg x,
    E.coordChange_symm (AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx)]

/-- The canonical isomorphisms between pullbacks are natural: they commute with the pullbacks
of an isomorphism of exponent systems. -/
theorem comapCongr_trans_comap {E' : ExponentSystem h B Γ'} (σ : E.Iso E')
    (f g : AtlasMap V B' B) (hfg : ⇑f = ⇑g) :
    (E.comapCongr f g hfg).trans (σ.comap g) = (σ.comap f).trans (E'.comapCongr f g hfg) := by
  ext e x hx γ
  have hm := AtlasMap.mem_chart_source_inter_of_coe_eq hfg hx
  rw [Iso.trans_app, Iso.trans_app, AddEquiv.trans_apply, AddEquiv.trans_apply, comapCongr_app,
    comapCongr_app, Iso.comap_app, Iso.comap_app, ← σ.app_coordChange hm]
  simp only [hfg]

end comapCongr

end Mei.Toric.ExponentSystem
