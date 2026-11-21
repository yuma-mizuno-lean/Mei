/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.TangentLattice
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Exponent systems on integral-affine charted spaces

Let `B` be a charted space whose chart changes are locally integral affine for the lattice
`N ⊆ V`. Its integral tangent lattice `Λ` is the local system with fibre `N` and transition
functions `Mei.Toric.tangentLatticeChange`. An exponent system (`Mei.Toric.ExponentSystem`)
is a lattice local system `Γ` with fibre a fixed abelian group, presented by locally constant
lattice automorphisms `T_Γ` between the frames of the charts of the atlas that satisfy the
cocycle identity, together with a projection `ρ_e : Γ → N` in the frame of each chart `e`
such that `ρ_{e'} ∘ T_Γ = T_Λ ∘ ρ_e` on every overlap. The projection `ρ_e` is constant on
the domain of each chart.

The tangent lattice itself, with `ρ = id`, is the exponent system
`Mei.Toric.ExponentSystem.tangent`, the case `Γ = Λ`. Its general frame-change laws give
`Mei.Toric.tangentLatticeChange_self` and `Mei.Toric.tangentLatticeChange_symm`; on the model
space `V` with its single chart every tangent frame change is the identity
(`Mei.Toric.tangentLatticeChange_modelSpace`). For a discrete fibre, the frame changes of an
exponent system are the transition functions of a fibre bundle core indexed by the atlas
(`Mei.Toric.ExponentSystem.toFiberBundleCore`), the lattice local system itself. The
focus-focus instance is `Mei.FocusFocus.exponentSystem`.

Lattice local systems over integral-affine manifolds with a map to the tangent lattice appear
in Gross–Siebert, *An Invitation to Toric Degenerations*, §2 (arXiv:0808.2749v2), and
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
§§1 and 3 (arXiv:1601.07081v4).
-/

public section

open Set Topology Manifold

namespace Mei.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- An exponent system on an integral-affine charted space `B`, with model fibre `Γ`: lattice
automorphisms `coordChange e e' x` of `Γ` from the frame of the chart `e` to that of `e'`,
locally constant on overlaps, satisfying the cocycle identity and trivial off the overlap,
and in the frame of each
chart a projection `ρ_e : Γ → N` to the integral tangent lattice, compatible with the tangent
frame changes. -/
structure ExponentSystem (h : TauCeti.Toric.IsIntegralLattice i) (B : Type*)
    [TopologicalSpace B] [ChartedSpace V B] [HasGroupoid B (integralAffineGroupoid h)]
    (Γ : Type*) [AddCommGroup Γ] where
  /-- The change of exponent frames from the first chart to the second at a point. -/
  coordChange : atlas V B → atlas V B → B → Γ ≃+ Γ
  /-- On triple overlaps, changing frames through an intermediate chart is the direct
  change. -/
  coordChange_trans {e e' e'' : atlas V B} {x : B} :
    x ∈ e.val.source ∩ e'.val.source ∩ e''.val.source →
      (coordChange e e' x).trans (coordChange e' e'' x) = coordChange e e'' x
  /-- The frame changes are locally constant on overlaps. -/
  eventually_coordChange_eq {e e' : atlas V B} {x : B} :
    x ∈ e.val.source ∩ e'.val.source → ∀ᶠ y in 𝓝 x, coordChange e e' y = coordChange e e' x
  /-- Off the overlap of the two chart domains, the frame change is the identity. -/
  coordChange_of_notMem {e e' : atlas V B} {x : B} :
    x ∉ e.val.source ∩ e'.val.source → coordChange e e' x = AddEquiv.refl Γ
  /-- The projection `ρ_e` to the integral tangent lattice in the frame of a chart. -/
  projection : atlas V B → Γ →+ N
  /-- On overlaps, `ρ_{e'} ∘ T_Γ = T_Λ ∘ ρ_e`. -/
  projection_coordChange {e e' : atlas V B} {x : B} :
    x ∈ e.val.source ∩ e'.val.source → ∀ γ : Γ,
      projection e' (coordChange e e' x γ) = tangentLatticeChange h e e' x (projection e γ)

variable {h : TauCeti.Toric.IsIntegralLattice i} {B : Type*} [TopologicalSpace B]
  [ChartedSpace V B] [HasGroupoid B (integralAffineGroupoid h)] {Γ : Type*} [AddCommGroup Γ]

namespace ExponentSystem

variable (E : ExponentSystem h B Γ)

/-- On its domain, the frame change from a chart to itself is the identity. -/
@[simp]
theorem coordChange_self {e : atlas V B} {x : B} (hx : x ∈ e.val.source) :
    E.coordChange e e x = AddEquiv.refl Γ := by
  have := E.coordChange_trans (e := e) (e' := e) (e'' := e) ⟨⟨hx, hx⟩, hx⟩
  ext γ
  exact (E.coordChange e e x).injective <| by
    simpa only [AddEquiv.trans_apply, AddEquiv.refl_apply] using DFunLike.congr_fun this γ

/-- Reversing the two charts inverts the frame change on the overlap. -/
theorem coordChange_symm {e e' : atlas V B} {x : B} (hx : x ∈ e.val.source ∩ e'.val.source) :
    E.coordChange e' e x = (E.coordChange e e' x).symm := by
  ext γ
  rw [AddEquiv.eq_symm_apply, ← AddEquiv.trans_apply, E.coordChange_trans ⟨⟨hx.2, hx.1⟩, hx.2⟩,
    E.coordChange_self hx.2, AddEquiv.refl_apply]

/-- Two exponent systems are equal when their frame changes agree on every overlap and their
projections agree in every chart. -/
@[ext]
theorem ext {E E' : ExponentSystem h B Γ}
    (hc : ∀ e e' : atlas V B, ∀ x ∈ e.val.source ∩ e'.val.source,
      E.coordChange e e' x = E'.coordChange e e' x)
    (hp : ∀ e, E.projection e = E'.projection e) : E = E' := by
  have hc' : E.coordChange = E'.coordChange := by
    funext e e' x
    by_cases hx : x ∈ e.val.source ∩ e'.val.source
    · exact hc e e' x hx
    · rw [E.coordChange_of_notMem hx, E'.coordChange_of_notMem hx]
  rcases E with ⟨c, _, _, _, ρ, _⟩
  rcases E' with ⟨c', _, _, _, ρ', _⟩
  obtain rfl : c = c' := hc'
  obtain rfl : ρ = ρ' := funext hp
  rfl

variable (h B) in
/-- The integral tangent lattice as an exponent system, with `ρ = id`. -/
noncomputable def tangent : ExponentSystem h B N where
  coordChange := tangentLatticeChange h
  coordChange_trans := tangentLatticeChange_trans
  eventually_coordChange_eq := eventually_tangentLatticeChange_eq
  coordChange_of_notMem := tangentLatticeChange_of_notMem
  projection _ := AddMonoidHom.id N
  projection_coordChange _ _ := rfl

/-- The frame changes of the tangent exponent system are the tangent frame changes. -/
@[simp]
theorem tangent_coordChange : (tangent h B).coordChange = tangentLatticeChange h := (rfl)

/-- The projections of the tangent exponent system are identities. -/
@[simp]
theorem tangent_projection (e : atlas V B) : (tangent h B).projection e = AddMonoidHom.id N :=
  (rfl)

end ExponentSystem

/-- On its domain, the tangent frame change from a chart to itself is the identity. -/
@[simp]
theorem tangentLatticeChange_self {e : atlas V B} {x : B} (hx : x ∈ e.val.source) :
    tangentLatticeChange h e e x = AddEquiv.refl N :=
  (ExponentSystem.tangent h B).coordChange_self hx

/-- Reversing the two charts inverts the tangent frame change on the overlap. -/
theorem tangentLatticeChange_symm {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    tangentLatticeChange h e' e x = (tangentLatticeChange h e e' x).symm :=
  (ExponentSystem.tangent h B).coordChange_symm hx

/-- In the one-chart case of the model space `V`, every tangent frame change is the
identity. -/
@[simp]
theorem tangentLatticeChange_modelSpace (e e' : atlas V V) (x : V) :
    tangentLatticeChange h e e' x = AddEquiv.refl N := by
  have he := chartedSpaceSelf_atlas.mp e.property
  obtain rfl : e = e' := Subtype.ext (he.trans (chartedSpaceSelf_atlas.mp e'.property).symm)
  exact tangentLatticeChange_self (by rw [he]; exact mem_univ x)

namespace ExponentSystem

variable (E : ExponentSystem h B Γ)

variable [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The lattice local system of an exponent system with discrete fibre: the fibre bundle core
over the atlas whose chart at `x` is `achart V x` and whose transition functions are the frame
changes. -/
noncomputable def toFiberBundleCore : FiberBundleCore (atlas V B) B Γ where
  baseSet e := e.val.source
  isOpen_baseSet e := e.val.open_source
  indexAt := achart V
  mem_baseSet_at := mem_chart_source V
  coordChange e e' x := E.coordChange e e' x
  coordChange_self _ _ hx γ := by rw [E.coordChange_self hx, AddEquiv.refl_apply]
  continuousOn_coordChange e e' := by
    rintro ⟨x, γ⟩ ⟨hx, -⟩
    have hc : Continuous fun q : B × Γ => E.coordChange e e' x q.2 :=
      continuous_of_discreteTopology.comp continuous_snd
    refine (hc.continuousAt.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [continuousAt_fst.eventually (E.eventually_coordChange_eq hx)] with q hq
    exact DFunLike.congr_fun hq q.2
  coordChange_comp _ _ _ _ hx γ := by
    rw [← AddEquiv.trans_apply, E.coordChange_trans hx]

/-- The trivializations of the lattice local system live over the chart domains. -/
@[simp]
theorem toFiberBundleCore_localTriv_baseSet (e : atlas V B) :
    (E.toFiberBundleCore.localTriv e).baseSet = e.val.source := (rfl)

/-- The preferred frame at a point is the chart at that point. -/
@[simp]
theorem toFiberBundleCore_indexAt (x : B) : E.toFiberBundleCore.indexAt x = achart V x := (rfl)

/-- The transition functions of the lattice local system are the frame changes. -/
@[simp]
theorem toFiberBundleCore_coordChange (e e' : atlas V B) (x : B) (γ : Γ) :
    E.toFiberBundleCore.coordChange e e' x γ = E.coordChange e e' x γ := (rfl)

end ExponentSystem

end Mei.Toric
