/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Manifold.IntegralAffine.Basic
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# The integral tangent lattice of an integral-affine atlas

A map that is locally integral affine on an open set has, at each point, a well-defined
integral linear part: every local integral affine witness at that point has the same lattice
equivalence (`Mei.Toric.IsLocallyIntegralAffineOn.latticeEquivAt_eq`). It is locally
constant in the point.

For a charted space `B` whose chart changes lie in `Mei.Toric.integralAffineGroupoid h`, the
lattice part of the chart change `e' ∘ e⁻¹` at `e x` is the change of integral tangent frames
from `e` to `e'` at `x` (`Mei.Toric.tangentLatticeChange`). These lattice automorphisms are
locally constant on overlaps and satisfy the cocycle identity, so they present the integral
tangent lattice local system `Λ` of the integral-affine structure on `B`.

This is the integral tangent lattice `Λ` of an integral-affine manifold in Gross–Siebert,
*An Invitation to Toric Degenerations*, §2 (arXiv:0808.2749v2), and Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §1 (arXiv:1601.07081v4).
-/

public section

open Set Topology Manifold

namespace Mei.Toric

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

namespace IsLocallyIntegralAffineOn

/-- The integral linear part at `x ∈ s` of a map that is locally integral affine on `s`: the
lattice equivalence of a local integral affine witness at `x`. On an open set it does not
depend on the witness (`latticeEquivAt_eq`). -/
noncomputable def latticeEquivAt {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) {x : V} (hx : x ∈ s) : N ≃+ N' :=
  (isLocallyIntegralAffineOn_iff.mp hf x hx).choose.latticeEquiv

/-- On an open set, the integral linear part at `x` is the lattice equivalence of every
integral affine equivalence agreeing with the map near `x`. -/
theorem latticeEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s)
    {e : IntegralAffineEquiv h h'} {u : Set V} (hu : IsOpen u) (hxu : x ∈ u)
    (he : EqOn f e (s ∩ u)) : hf.latticeEquivAt hx = e.latticeEquiv := by
  obtain ⟨u₀, hu₀, hxu₀, he₀⟩ := (isLocallyIntegralAffineOn_iff.mp hf x hx).choose_spec
  have hO : IsOpen (s ∩ (u ∩ u₀)) := hs.inter (hu.inter hu₀)
  rw [latticeEquivAt, IntegralAffineEquiv.eq_of_eqOn_open hO ⟨x, hx, hxu, hxu₀⟩
    fun y hy => (he₀ ⟨hy.1, hy.2.2⟩).symm.trans (he ⟨hy.1, hy.2.1⟩)]

/-- On an open set, the integral linear part is locally constant. -/
theorem eventually_latticeEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ s, hf.latticeEquivAt hy = hf.latticeEquivAt hx := by
  obtain ⟨u, hu, hxu, he⟩ := (isLocallyIntegralAffineOn_iff.mp hf x hx).choose_spec
  filter_upwards [hu.mem_nhds hxu] with y hyu hy
  rw [hf.latticeEquivAt_eq hs hy hu hyu he, hf.latticeEquivAt_eq hs hx hu hxu he]

end IsLocallyIntegralAffineOn

variable (h) {B : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [HasGroupoid B (integralAffineGroupoid h)]

/-- The chart change between two charts of an integral-affine atlas is locally integral
affine on its source. -/
theorem isLocallyIntegralAffineOn_symm_trans (e e' : atlas V B) :
    IsLocallyIntegralAffineOn h h (e.1.symm ≫ₕ e'.1) (e.1.symm ≫ₕ e'.1).source :=
  mem_integralAffineGroupoid_iff_forward.mp
    ((integralAffineGroupoid h).compatible e.2 e'.2)

open Classical in
/-- The change of integral tangent frames from the chart `e` to the chart `e'` at `x`: the
integral linear part of the chart change `e' ∘ e⁻¹` at `e x`. It is the identity off the
overlap of the two chart domains. -/
noncomputable def tangentLatticeChange (e e' : atlas V B) (x : B) : N ≃+ N :=
  if hx : x ∈ e.1.source ∩ e'.1.source then
    (isLocallyIntegralAffineOn_symm_trans h e e').latticeEquivAt
      (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2)
  else AddEquiv.refl N

variable {h}

/-- On the overlap, the tangent frame change is the integral linear part of the chart change
at `e x`. -/
theorem tangentLatticeChange_of_mem {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    tangentLatticeChange h e e' x = (isLocallyIntegralAffineOn_symm_trans h e e').latticeEquivAt
      (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2) := by
  simp only [tangentLatticeChange, hx, ↓reduceDIte]

/-- On the overlap, the tangent frame change is the lattice equivalence of every integral
affine equivalence agreeing with the chart change near `e x`. -/
theorem tangentLatticeChange_eq {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source)
    {a : IntegralAffineEquiv h h} {u : Set V} (hu : IsOpen u) (hxu : e.1 x ∈ u)
    (ha : EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u)) :
    tangentLatticeChange h e e' x = a.latticeEquiv := by
  rw [tangentLatticeChange_of_mem hx]
  exact (isLocallyIntegralAffineOn_symm_trans h e e').latticeEquivAt_eq
    (e.1.symm ≫ₕ e'.1).open_source _ hu hxu ha

/-- Off the overlap of the two chart domains, the tangent frame change is the identity. -/
theorem tangentLatticeChange_of_notMem {e e' : atlas V B} {x : B}
    (hx : x ∉ e.1.source ∩ e'.1.source) : tangentLatticeChange h e e' x = AddEquiv.refl N := by
  simp only [tangentLatticeChange, hx, ↓reduceDIte]

/-- Every point of the overlap has a local integral affine witness for the chart change. -/
theorem exists_tangentLatticeChange_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∃ a : IntegralAffineEquiv h h, ∃ u : Set V, IsOpen u ∧ e.1 x ∈ u ∧
      EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u) ∧
      tangentLatticeChange h e e' x = a.latticeEquiv := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (isLocallyIntegralAffineOn_symm_trans h e e') (e.1 x)
    (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2)
  exact ⟨a, u, hu, hxu, ha, tangentLatticeChange_eq hx hu hxu ha⟩

/-- The tangent frame change is locally constant on the overlap of the chart domains. -/
theorem eventually_tangentLatticeChange_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∀ᶠ y in 𝓝 x, tangentLatticeChange h e e' y = tangentLatticeChange h e e' x := by
  filter_upwards [(e.1.open_source.inter e'.1.open_source).mem_nhds hx,
    (e.1.continuousAt hx.1).eventually
      ((isLocallyIntegralAffineOn_symm_trans h e e').eventually_latticeEquivAt_eq
        (e.1.symm ≫ₕ e'.1).open_source
        (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2))] with y hy hy'
  rw [tangentLatticeChange_of_mem hy, tangentLatticeChange_of_mem hx]
  exact hy' _

/-- The tangent frame changes satisfy the cocycle identity on triple overlaps: changing from
`e` to `e'` and then to `e''` is the change from `e` to `e''`. -/
theorem tangentLatticeChange_trans {e e' e'' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source ∩ e''.1.source) :
    (tangentLatticeChange h e e' x).trans (tangentLatticeChange h e' e'' x) =
      tangentLatticeChange h e e'' x := by
  obtain ⟨a, u, hu, hxu, ha, hx₁⟩ := exists_tangentLatticeChange_eq (h := h) hx.1
  obtain ⟨b, v, hv, hxv, hb, hx₂⟩ := exists_tangentLatticeChange_eq (h := h) ⟨hx.1.2, hx.2⟩
  have hex : e.1.symm (e.1 x) = x := e.1.left_inv hx.1.1
  have hax : a (e.1 x) = e'.1 x := by
    exact (ha ⟨PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1.1 hx.1.2,
      hxu⟩).symm.trans (congrArg e'.1 hex)
  have hO : IsOpen (u ∩ a ⁻¹' v ∩ (e.1.target ∩ e.1.symm ⁻¹' e'.1.source)) :=
    (hu.inter (hv.preimage a.continuous)).inter (e.1.isOpen_inter_preimage_symm e'.1.open_source)
  have hxO : e.1 x ∈ u ∩ a ⁻¹' v ∩ (e.1.target ∩ e.1.symm ⁻¹' e'.1.source) :=
    ⟨⟨hxu, by simpa only [mem_preimage, hax] using hxv⟩, e.1.map_source hx.1.1,
      by simpa only [mem_preimage, hex] using hx.1.2⟩
  rw [hx₁, hx₂, tangentLatticeChange_eq (a := a.trans b) ⟨hx.1.1, hx.2⟩ hO hxO,
    IntegralAffineEquiv.trans_latticeEquiv]
  intro y ⟨hy, hyO⟩
  have hy' : y ∈ (e.1.symm ≫ₕ e'.1).source := ⟨hy.1, hyO.2.2⟩
  have hz : e'.1 (e.1.symm y) ∈ (e'.1.symm ≫ₕ e''.1).source := by
    refine ⟨e'.1.map_source hyO.2.2, ?_⟩
    exact (congrArg (· ∈ e''.1.source) (e'.1.left_inv hyO.2.2)).mpr hy.2
  have hay : (e.1.symm ≫ₕ e'.1) y = a y := ha ⟨hy', hyO.1.1⟩
  rw [OpenPartialHomeomorph.trans_apply] at hay
  have hby := hb ⟨hz, by simpa only [mem_preimage, hay] using hyO.1.2⟩
  rw [OpenPartialHomeomorph.trans_apply, e'.1.left_inv hyO.2.2, hay] at hby
  rw [OpenPartialHomeomorph.trans_apply, hby, IntegralAffineEquiv.trans_toAffineEquiv,
    AffineEquiv.trans_apply]

end Mei.Toric
