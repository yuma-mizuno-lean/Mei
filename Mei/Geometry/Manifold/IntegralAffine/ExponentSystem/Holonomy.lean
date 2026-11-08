/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.DevelopingMap.Holonomy
public import Mei.Geometry.Manifold.IntegralAffine.ExponentSystem.Trivialization

/-!
# Transitions and holonomy of trivializations of exponent systems

On a connected integral-affine charted space `B`, two trivializations `τ`, `τ'` of an exponent
system `E` (with model fibres `Γ₀`, `Γ₀'`) differ by a unique lattice isomorphism
`τ.transition τ' : Γ₀ ≃+ Γ₀'`: in every chart `e` and at every point `x` of its domain,
`τ'_e(x) = τ_e(x)` followed by this isomorphism
(`Mei.Toric.ExponentSystem.Trivialization.existsUnique_frame_eq`). The proof is that the frame
changes `τ_e(x)⁻¹ ≫ τ'_e(x)` do not depend on the chart and are locally constant, hence constant.
Transitions are the identity from a trivialization to itself, compose, and invert
(`transition_self`, `transition_trans`, `transition_symm`); they do not change when both
trivializations are pulled back along an atlas map (`transition_comap`).

For an atlas self-map `f` of `B`, for instance a deck transformation of a universal cover, and an
isomorphism `σ : (E.comap f).Iso E` identifying the fibre of `E` at `f x` with the fibre at `x`,
the *holonomy* `τ.holonomy f σ : AddAut Γ₀` is the transition from the pullback of `τ` along `σ` to
the pullback of `τ` along `f`. It is characterized by the equivariance
`τ_{f(e)}(f x) γ = holonomy (τ_e(x) (σ_e(x) γ))` (`holonomy_apply`), is trivial for the identity
(`holonomy_id`) and multiplicative in `f` (`holonomy_comp`), with the isomorphisms composed in the
fibrewise sense. If a trivialization is compatible with the projections to the tangent lattice
along a developing map `dev`, its holonomy intertwines the projection `ρ₀ : Γ₀ → N` with the
lattice part of the integral affine holonomy of `dev` (`projection_holonomy`): this is the
compatibility `T_Λ ρ = ρ' T_Γ` of lattice and tangent data on the universal cover. For the tangent
lattice itself, the holonomy of the tangent trivialization of `dev` is the lattice part of
`dev.holonomy f` (`tangentTrivialization_holonomy`).

This is the equivariance of trivializations of lifted lattice local systems under deck
transformations in Gross–Siebert, *An Invitation to Toric Degenerations*, §2
(arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §§1 and 3 (arXiv:1601.07081v4); it parallels the holonomy of developing
maps `Mei.Toric.DevelopingMap.holonomy`.
-/

public section

open Set Topology Manifold

namespace Mei.Toric.ExponentSystem.Trivialization

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {B B' : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [HasGroupoid B (integralAffineGroupoid h)]
  [TopologicalSpace B'] [ChartedSpace V B'] [HasGroupoid B' (integralAffineGroupoid h)]
  {Γ : Type*} [AddCommGroup Γ] {Γ₀ Γ₀' Γ₀'' : Type*} [AddCommGroup Γ₀] [AddCommGroup Γ₀']
  [AddCommGroup Γ₀''] {E : ExponentSystem h B Γ}

/-- The frame change `τ_e(x)⁻¹ ≫ τ'_e(x)` between two trivializations does not depend on the
chart. -/
private theorem frame_symm_trans_frame_eq (τ : E.Trivialization Γ₀) (τ' : E.Trivialization Γ₀')
    {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    (τ.frame e' x hx.2).symm.trans (τ'.frame e' x hx.2) =
      (τ.frame e x hx.1).symm.trans (τ'.frame e x hx.1) := by
  ext γ₀
  obtain ⟨γ, rfl⟩ := (τ.frame e x hx.1).surjective γ₀
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    ← τ.frame_coordChange hx γ, AddEquiv.symm_apply_apply, τ'.frame_coordChange hx]

section Transition

variable [ConnectedSpace B]

/-- On a connected space, two trivializations of an exponent system differ by a unique lattice
isomorphism of the model fibres, in every chart and at every point. -/
theorem existsUnique_frame_eq (τ : E.Trivialization Γ₀) (τ' : E.Trivialization Γ₀') :
    ∃! c : Γ₀ ≃+ Γ₀', ∀ e x (hx : x ∈ e.1.source),
      τ'.frame e x hx = (τ.frame e x hx).trans c := by
  let g : B → (Γ₀ ≃+ Γ₀') := fun x =>
    (τ.frame (achart V x) x (mem_achart_source V x)).symm.trans
      (τ'.frame (achart V x) x (mem_achart_source V x))
  have hg (e : atlas V B) (x : B) (hx : x ∈ e.1.source) :
      g x = (τ.frame e x hx).symm.trans (τ'.frame e x hx) :=
    frame_symm_trans_frame_eq τ τ' ⟨hx, mem_achart_source V x⟩
  have hloc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx := mem_achart_source V x
    filter_upwards [(achart V x).1.open_source.mem_nhds hx, τ.eventually_frame_eq hx,
      τ'.eventually_frame_eq hx] with y hy hτ hτ'
    rw [hg (achart V x) y hy, hτ hy, hτ' hy, hg (achart V x) x hx]
  have hconst (x : B) : g x = g (Classical.arbitrary B) :=
    hloc.apply_eq_of_preconnectedSpace _ _
  have hfr (e : atlas V B) (x : B) (hx : x ∈ e.1.source) :
      τ'.frame e x hx = (τ.frame e x hx).trans (g (Classical.arbitrary B)) := by
    rw [← hconst x, hg e x hx]
    ext γ
    simp
  refine ⟨g (Classical.arbitrary B), hfr, fun c hc => ?_⟩
  set x₀ := Classical.arbitrary B
  have hx₀ := mem_achart_source V x₀
  ext γ₀
  obtain ⟨γ, rfl⟩ := (τ.frame (achart V x₀) x₀ hx₀).surjective γ₀
  have := DFunLike.congr_fun (hc _ x₀ hx₀) γ
  have h0 := DFunLike.congr_fun (hfr _ x₀ hx₀) γ
  rw [AddEquiv.trans_apply] at this h0
  exact this.symm.trans h0

variable (τ : E.Trivialization Γ₀) (τ' : E.Trivialization Γ₀')

/-- The lattice isomorphism carrying the frames of one trivialization of an exponent system to
those of another on a connected space. -/
noncomputable def transition : Γ₀ ≃+ Γ₀' :=
  (existsUnique_frame_eq τ τ').exists.choose

variable {τ τ'}

/-- The transition of two trivializations is the unique lattice isomorphism carrying the frames of
the first to those of the second. -/
theorem transition_eq_iff {c : Γ₀ ≃+ Γ₀'} :
    τ.transition τ' = c ↔
      ∀ e x (hx : x ∈ e.1.source), τ'.frame e x hx = (τ.frame e x hx).trans c :=
  ⟨fun hc => hc ▸ (existsUnique_frame_eq τ τ').exists.choose_spec,
    fun hc => (existsUnique_frame_eq τ τ').unique
      (existsUnique_frame_eq τ τ').exists.choose_spec hc⟩

variable (τ τ')

/-- The transition carries the frames of the first trivialization to those of the second. -/
theorem frame_eq_trans_transition (e : atlas V B) (x : B) (hx : x ∈ e.1.source) :
    τ'.frame e x hx = (τ.frame e x hx).trans (τ.transition τ') :=
  transition_eq_iff.mp rfl e x hx

/-- The transition from a trivialization to itself is the identity. -/
@[simp]
theorem transition_self : τ.transition τ = AddEquiv.refl Γ₀ :=
  transition_eq_iff.mpr fun e x hx => by
    ext γ
    simp

/-- Transitions compose. -/
theorem transition_trans (τ'' : E.Trivialization Γ₀'') :
    τ.transition τ'' = (τ.transition τ').trans (τ'.transition τ'') :=
  transition_eq_iff.mpr fun e x hx => by
    rw [frame_eq_trans_transition τ' τ'' e x hx, frame_eq_trans_transition τ τ' e x hx]
    ext γ
    simp

/-- The transition in the reverse direction is the inverse. -/
theorem transition_symm : τ'.transition τ = (τ.transition τ').symm :=
  transition_eq_iff.mpr fun e x hx => by
    ext γ
    rw [AddEquiv.trans_apply, AddEquiv.eq_symm_apply, ← AddEquiv.trans_apply,
      ← frame_eq_trans_transition τ τ' e x hx]

/-- The transition of two trivializations is unchanged by pulling both back along an atlas map
from a connected space. -/
theorem transition_comap [ConnectedSpace B'] (f : AtlasMap V B' B) :
    (τ.comap f).transition (τ'.comap f) = τ.transition τ' :=
  transition_eq_iff.mpr fun e x hx => by
    rw [comap_frame, comap_frame, frame_eq_trans_transition τ τ']

end Transition

section Holonomy

variable [ConnectedSpace B] {τ : E.Trivialization Γ₀} (f : AtlasMap V B B)
  (σ : (E.comap f).Iso E)

/-- The holonomy of a trivialization `τ` of an exponent system along an atlas self-map `f` of a
connected space, relative to an isomorphism `σ : (E.comap f).Iso E` identifying the fibres of `E`
at `f x` and at `x`: the transition from the pullback of `τ` along `σ` to the pullback of `τ`
along `f`. For a deck transformation `f` of a universal cover it is the action of `f` on the
model fibre. -/
noncomputable def holonomy (τ : E.Trivialization Γ₀) : Γ₀ ≃+ Γ₀ :=
  (ofIso σ τ).transition (τ.comap f)

/-- The holonomy is the unique automorphism of the model fibre carrying the frame of `τ` at `x`,
precomposed with `σ`, to its frame at `f x`. -/
theorem holonomy_eq_iff {c : Γ₀ ≃+ Γ₀} :
    τ.holonomy f σ = c ↔ ∀ e x (hx : x ∈ e.1.source),
      τ.frame (f.chart e) (f x) ((f.mem_source_iff e).mp hx) =
        ((σ.app e x hx).trans (τ.frame e x hx)).trans c := by
  rw [holonomy, transition_eq_iff]
  simp only [comap_frame, ofIso_frame]

/-- A trivialization is equivariant under an atlas self-map of a connected space: its frame at
`f x` is the holonomy applied to its frame at `x`, after identifying the fibres by `σ`. -/
theorem holonomy_apply (e : atlas V B) (x : B) (hx : x ∈ e.1.source) (γ : Γ) :
    τ.frame (f.chart e) (f x) ((f.mem_source_iff e).mp hx) γ =
      τ.holonomy f σ (τ.frame e x hx (σ.app e x hx γ)) :=
  DFunLike.congr_fun ((holonomy_eq_iff f σ).mp rfl e x hx) γ

/-- The holonomy along the identity atlas map is trivial, for the identity identification of the
fibres. -/
theorem holonomy_id (σ : (E.comap (AtlasMap.id V B)).Iso E)
    (hσ : ∀ e x (hx : x ∈ e.1.source) γ, σ.app e x hx γ = γ) :
    τ.holonomy (AtlasMap.id V B) σ = AddEquiv.refl Γ₀ :=
  (holonomy_eq_iff _ σ).mpr fun e x hx => by
    ext γ
    simp [hσ]

/-- The holonomy is multiplicative in the atlas self-map, when the identification of fibres along a
composite is the composite of the identifications. -/
theorem holonomy_comp (g : AtlasMap V B B) (σg : (E.comap g).Iso E)
    (σgf : (E.comap (g.comp f)).Iso E)
    (hσ : ∀ e x (hx : x ∈ e.1.source) γ, σgf.app e x hx γ =
      σ.app e x hx (σg.app (f.chart e) (f x) ((f.mem_source_iff e).mp hx) γ)) :
    τ.holonomy (g.comp f) σgf = (τ.holonomy f σ).trans (τ.holonomy g σg) :=
  (holonomy_eq_iff _ σgf).mpr fun e x hx => by
    ext γ
    rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply, hσ,
      ← holonomy_apply f σ e x hx, ← holonomy_apply g σg (f.chart e) (f x)]
    simp only [AtlasMap.comp_chart, AtlasMap.coe_comp, Function.comp_apply]

/-- If the frames of a trivialization are compatible with a map `ρ₀` to the tangent lattice and
the tangent frames of a developing map `dev`, then the holonomy intertwines `ρ₀` with the lattice
part of the integral affine holonomy of `dev`. -/
theorem projection_holonomy (dev : DevelopingMap h B) (ρ₀ : Γ₀ →+ N)
    (hρ : ∀ e x (hx : x ∈ e.1.source) γ,
      ρ₀ (τ.frame e x hx γ) = dev.tangentFrame e x hx (E.projection e γ)) (γ₀ : Γ₀) :
    ρ₀ (τ.holonomy f σ γ₀) = (dev.holonomy f).latticeEquiv (ρ₀ γ₀) := by
  set x := Classical.arbitrary B
  have hx := mem_achart_source V x
  obtain ⟨γ, rfl⟩ := (τ.frame (achart V x) x hx).surjective γ₀
  obtain ⟨γ', rfl⟩ := (σ.app (achart V x) x hx).surjective γ
  have hp := σ.projection_app hx γ'
  rw [comap_projection] at hp
  rw [← holonomy_apply f σ, hρ, hρ, ← hp,
    dev.tangentFrame_chart_eq_trans_holonomy_latticeEquiv f (achart V x) x hx,
    AddEquiv.trans_apply]

/-- The holonomy of the tangent trivialization of a developing map is the lattice part of the
integral affine holonomy. -/
theorem tangentTrivialization_holonomy (dev : DevelopingMap h B)
    (σ : ((ExponentSystem.tangent h B).comap f).Iso (ExponentSystem.tangent h B)) :
    dev.tangentTrivialization.holonomy f σ = (dev.holonomy f).latticeEquiv :=
  AddEquiv.ext fun γ₀ => projection_holonomy f σ dev (AddMonoidHom.id N)
    (fun _ _ _ _ => by simp) γ₀

end Holonomy

end Mei.Toric.ExponentSystem.Trivialization
