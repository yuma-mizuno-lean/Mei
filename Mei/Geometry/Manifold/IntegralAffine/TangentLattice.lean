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
integral affine equivalence germ: every local integral affine witness at that point is the
same equivalence (`Mei.Toric.IsLocallyIntegralAffineOn.affineEquivAt_eq`), and it is locally
constant in the point. Its integral linear part is `latticeEquivAt`.

For a charted space `B` whose chart changes lie in `Mei.Toric.integralAffineGroupoid h`, the
chart change `e' ∘ e⁻¹` at `e x` is such an equivalence (`Mei.Toric.chartChange`). These
group-valued chart changes are locally constant on overlaps and satisfy the cocycle identity
(`Mei.Toric.chartChange_trans`). Their lattice parts are the changes of integral tangent
frames from `e` to `e'` at `x` (`Mei.Toric.tangentLatticeChange`); they present the integral
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

/-- The integral affine equivalence of a local witness at `x ∈ s` of a map that is locally
integral affine on `s`. On an open set it does not depend on the witness
(`affineEquivAt_eq`). -/
noncomputable def affineEquivAt {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) {x : V} (hx : x ∈ s) : IntegralAffineEquiv h h' :=
  (isLocallyIntegralAffineOn_iff.mp hf x hx).choose

/-- On an open set, the local witness at `x` is every integral affine equivalence agreeing with
the map near `x`. -/
theorem affineEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s)
    {e : IntegralAffineEquiv h h'} {u : Set V} (hu : IsOpen u) (hxu : x ∈ u)
    (he : EqOn f e (s ∩ u)) : hf.affineEquivAt hx = e := by
  obtain ⟨u₀, hu₀, hxu₀, he₀⟩ := (isLocallyIntegralAffineOn_iff.mp hf x hx).choose_spec
  have hO : IsOpen (s ∩ (u ∩ u₀)) := hs.inter (hu.inter hu₀)
  exact IntegralAffineEquiv.eq_of_eqOn_open hO ⟨x, hx, hxu, hxu₀⟩
    fun y hy => (he₀ ⟨hy.1, hy.2.2⟩).symm.trans (he ⟨hy.1, hy.2.1⟩)

/-- The local witness at `x` agrees with the map at `x`. -/
@[simp]
theorem affineEquivAt_apply {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) {x : V} (hx : x ∈ s) :
    hf.affineEquivAt hx x = f x := by
  obtain ⟨_, _, hxu, he⟩ := (isLocallyIntegralAffineOn_iff.mp hf x hx).choose_spec
  exact (he ⟨hx, hxu⟩).symm

/-- On an open set, the local witness is locally constant. -/
theorem eventually_affineEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ s, hf.affineEquivAt hy = hf.affineEquivAt hx := by
  obtain ⟨u, hu, hxu, he⟩ := (isLocallyIntegralAffineOn_iff.mp hf x hx).choose_spec
  filter_upwards [hu.mem_nhds hxu] with y hyu hy
  rw [hf.affineEquivAt_eq hs hy hu hyu he]
  exact hf.affineEquivAt_eq hs hx hu hxu he

/-- The integral linear part at `x ∈ s` of a map that is locally integral affine on `s`: the
lattice equivalence of its local witness at `x`. -/
noncomputable def latticeEquivAt {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) {x : V} (hx : x ∈ s) : N ≃+ N' :=
  (hf.affineEquivAt hx).latticeEquiv

/-- On an open set, the integral linear part at `x` is the lattice equivalence of every
integral affine equivalence agreeing with the map near `x`. -/
theorem latticeEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s)
    {e : IntegralAffineEquiv h h'} {u : Set V} (hu : IsOpen u) (hxu : x ∈ u)
    (he : EqOn f e (s ∩ u)) : hf.latticeEquivAt hx = e.latticeEquiv :=
  congrArg IntegralAffineEquiv.latticeEquiv (hf.affineEquivAt_eq hs hx hu hxu he)

/-- On an open set, the integral linear part is locally constant. -/
theorem eventually_latticeEquivAt_eq {f : V → W} {s : Set V}
    (hf : IsLocallyIntegralAffineOn h h' f s) (hs : IsOpen s) {x : V} (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ s, hf.latticeEquivAt hy = hf.latticeEquivAt hx := by
  filter_upwards [hf.eventually_affineEquivAt_eq hs hx] with y hy hy'
  rw [latticeEquivAt, latticeEquivAt, hy hy']

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
/-- The chart change from the chart `e` to the chart `e'` at `x`: the integral affine
equivalence agreeing with `e' ∘ e⁻¹` near `e x`. It is the identity off the overlap of the two
chart domains. -/
noncomputable def chartChange (e e' : atlas V B) (x : B) : IntegralAffineEquiv h h :=
  if hx : x ∈ e.1.source ∩ e'.1.source then
    (isLocallyIntegralAffineOn_symm_trans h e e').affineEquivAt
      (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2)
  else 1

variable {h}

/-- On the overlap, the chart change is the local witness of `e' ∘ e⁻¹` at `e x`. -/
theorem chartChange_of_mem {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    chartChange h e e' x = (isLocallyIntegralAffineOn_symm_trans h e e').affineEquivAt
      (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2) := by
  simp only [chartChange, hx, ↓reduceDIte]

/-- Off the overlap of the two chart domains, the chart change is the identity. -/
theorem chartChange_of_notMem {e e' : atlas V B} {x : B} (hx : x ∉ e.1.source ∩ e'.1.source) :
    chartChange h e e' x = 1 := by
  simp only [chartChange, hx, ↓reduceDIte]

/-- On the overlap, the chart change is every integral affine equivalence agreeing with the
chart change `e' ∘ e⁻¹` near `e x`. -/
theorem chartChange_eq {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source)
    {a : IntegralAffineEquiv h h} {u : Set V} (hu : IsOpen u) (hxu : e.1 x ∈ u)
    (ha : EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u)) :
    chartChange h e e' x = a := by
  rw [chartChange_of_mem hx]
  exact (isLocallyIntegralAffineOn_symm_trans h e e').affineEquivAt_eq
    (e.1.symm ≫ₕ e'.1).open_source _ hu hxu ha

/-- Every point of the overlap has a local integral affine witness for the chart change, and
the chart change at the point is that witness. -/
theorem exists_chartChange_eq {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∃ a : IntegralAffineEquiv h h, ∃ u : Set V, IsOpen u ∧ e.1 x ∈ u ∧
      EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u) ∧ chartChange h e e' x = a := by
  obtain ⟨a, u, hu, hxu, ha⟩ := isLocallyIntegralAffineOn_iff.mp
    (isLocallyIntegralAffineOn_symm_trans h e e') (e.1 x)
    (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2)
  exact ⟨a, u, hu, hxu, ha, chartChange_eq hx hu hxu ha⟩

/-- The chart change carries the point `e x` to `e' x`. -/
@[simp]
theorem chartChange_apply {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    chartChange h e e' x (e.1 x) = e'.1 x := by
  rw [chartChange_of_mem hx]
  exact ((isLocallyIntegralAffineOn_symm_trans h e e').affineEquivAt_apply _).trans
    (congrArg e'.1 (e.1.left_inv hx.1))

/-- The chart change is locally constant on the overlap of the chart domains. -/
theorem eventually_chartChange_eq {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∀ᶠ y in 𝓝 x, chartChange h e e' y = chartChange h e e' x := by
  filter_upwards [(e.1.open_source.inter e'.1.open_source).mem_nhds hx,
    (e.1.continuousAt hx.1).eventually
      ((isLocallyIntegralAffineOn_symm_trans h e e').eventually_affineEquivAt_eq
        (e.1.symm ≫ₕ e'.1).open_source
        (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2))] with y hy hy'
  rw [chartChange_of_mem hy, chartChange_of_mem hx]
  exact hy' _

/-- The chart changes satisfy the cocycle identity on triple overlaps: changing from `e` to `e'`
and then to `e''` is the change from `e` to `e''`. -/
theorem chartChange_trans {e e' e'' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source ∩ e''.1.source) :
    chartChange h e' e'' x * chartChange h e e' x = chartChange h e e'' x := by
  obtain ⟨a, u, hu, hxu, ha, hx₁⟩ := exists_chartChange_eq (h := h) hx.1
  obtain ⟨b, v, hv, hxv, hb, hx₂⟩ := exists_chartChange_eq (h := h) ⟨hx.1.2, hx.2⟩
  have hex : e.1.symm (e.1 x) = x := e.1.left_inv hx.1.1
  have hax : a (e.1 x) = e'.1 x := by
    exact (ha ⟨PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1.1 hx.1.2,
      hxu⟩).symm.trans (congrArg e'.1 hex)
  have hO : IsOpen (u ∩ a ⁻¹' v ∩ (e.1.target ∩ e.1.symm ⁻¹' e'.1.source)) :=
    (hu.inter (hv.preimage a.continuous)).inter (e.1.isOpen_inter_preimage_symm e'.1.open_source)
  have hxO : e.1 x ∈ u ∩ a ⁻¹' v ∩ (e.1.target ∩ e.1.symm ⁻¹' e'.1.source) :=
    ⟨⟨hxu, by simpa only [mem_preimage, hax] using hxv⟩, e.1.map_source hx.1.1,
      by simpa only [mem_preimage, hex] using hx.1.2⟩
  rw [hx₁, hx₂, (chartChange_eq (a := b * a) ⟨hx.1.1, hx.2⟩ hO hxO ?_).symm]
  intro y ⟨hy, hyO⟩
  have hy' : y ∈ (e.1.symm ≫ₕ e'.1).source := ⟨hy.1, hyO.2.2⟩
  have hz : e'.1 (e.1.symm y) ∈ (e'.1.symm ≫ₕ e''.1).source := by
    refine ⟨e'.1.map_source hyO.2.2, ?_⟩
    exact (congrArg (· ∈ e''.1.source) (e'.1.left_inv hyO.2.2)).mpr hy.2
  have hay : (e.1.symm ≫ₕ e'.1) y = a y := ha ⟨hy', hyO.1.1⟩
  rw [OpenPartialHomeomorph.trans_apply] at hay
  have hby := hb ⟨hz, by simpa only [mem_preimage, hay] using hyO.1.2⟩
  rw [OpenPartialHomeomorph.trans_apply, e'.1.left_inv hyO.2.2, hay] at hby
  rw [OpenPartialHomeomorph.trans_apply, hby, IntegralAffineEquiv.mul_apply]

/-- The chart change from a chart to itself is the identity. -/
@[simp]
theorem chartChange_self (e : atlas V B) (x : B) : chartChange h e e x = 1 := by
  by_cases hx : x ∈ e.1.source
  · refine chartChange_eq ⟨hx, hx⟩ (a := 1) isOpen_univ (mem_univ _) fun y hy => ?_
    rw [IntegralAffineEquiv.one_apply, OpenPartialHomeomorph.trans_apply]
    exact e.1.right_inv hy.1.1
  · exact chartChange_of_notMem fun hx' => hx hx'.1

/-- Reversing the two charts inverts the chart change. -/
theorem chartChange_symm {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source) :
    chartChange h e' e x = (chartChange h e e' x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, chartChange_trans (e'' := e) ⟨hx, hx.1⟩, chartChange_self]

variable (h)

/-- The change of integral tangent frames from the chart `e` to the chart `e'` at `x`: the
integral linear part of the chart change `e' ∘ e⁻¹` at `e x`. It is the identity off the
overlap of the two chart domains. -/
noncomputable def tangentLatticeChange (e e' : atlas V B) (x : B) : N ≃+ N :=
  (chartChange h e e' x).latticeEquiv

variable {h}

/-- On the overlap, the tangent frame change is the integral linear part of the chart change
at `e x`. -/
theorem tangentLatticeChange_of_mem {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    tangentLatticeChange h e e' x = (isLocallyIntegralAffineOn_symm_trans h e e').latticeEquivAt
      (PartialEquiv.mem_symm_trans_source e.1.toPartialEquiv hx.1 hx.2) := by
  rw [tangentLatticeChange, chartChange_of_mem hx]
  rfl

/-- On the overlap, the tangent frame change is the lattice equivalence of every integral
affine equivalence agreeing with the chart change near `e x`. -/
theorem tangentLatticeChange_eq {e e' : atlas V B} {x : B} (hx : x ∈ e.1.source ∩ e'.1.source)
    {a : IntegralAffineEquiv h h} {u : Set V} (hu : IsOpen u) (hxu : e.1 x ∈ u)
    (ha : EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u)) :
    tangentLatticeChange h e e' x = a.latticeEquiv :=
  congrArg IntegralAffineEquiv.latticeEquiv (chartChange_eq hx hu hxu ha)

/-- Off the overlap of the two chart domains, the tangent frame change is the identity. -/
theorem tangentLatticeChange_of_notMem {e e' : atlas V B} {x : B}
    (hx : x ∉ e.1.source ∩ e'.1.source) : tangentLatticeChange h e e' x = AddEquiv.refl N := by
  rw [tangentLatticeChange, chartChange_of_notMem hx, IntegralAffineEquiv.one_latticeEquiv]

/-- Every point of the overlap has a local integral affine witness for the chart change. -/
theorem exists_tangentLatticeChange_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∃ a : IntegralAffineEquiv h h, ∃ u : Set V, IsOpen u ∧ e.1 x ∈ u ∧
      EqOn (e.1.symm ≫ₕ e'.1) a ((e.1.symm ≫ₕ e'.1).source ∩ u) ∧
      tangentLatticeChange h e e' x = a.latticeEquiv := by
  obtain ⟨a, u, hu, hxu, ha, hxa⟩ := exists_chartChange_eq (h := h) hx
  exact ⟨a, u, hu, hxu, ha, congrArg IntegralAffineEquiv.latticeEquiv hxa⟩

/-- The tangent frame change is locally constant on the overlap of the chart domains. -/
theorem eventually_tangentLatticeChange_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source) :
    ∀ᶠ y in 𝓝 x, tangentLatticeChange h e e' y = tangentLatticeChange h e e' x := by
  filter_upwards [eventually_chartChange_eq (h := h) hx] with y hy
  rw [tangentLatticeChange, tangentLatticeChange, hy]

/-- The tangent frame changes satisfy the cocycle identity on triple overlaps: changing from
`e` to `e'` and then to `e''` is the change from `e` to `e''`. -/
theorem tangentLatticeChange_trans {e e' e'' : atlas V B} {x : B}
    (hx : x ∈ e.1.source ∩ e'.1.source ∩ e''.1.source) :
    (tangentLatticeChange h e e' x).trans (tangentLatticeChange h e' e'' x) =
      tangentLatticeChange h e e'' x := by
  rw [tangentLatticeChange, tangentLatticeChange, tangentLatticeChange, ← chartChange_trans hx,
    IntegralAffineEquiv.mul_latticeEquiv]

end Mei.Toric
