/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Atlas
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.GroupCocycle

/-!
# Lattice local systems of the focus-focus puncture

The exponent and integral tangent lattices are discrete bundles on the punctured
plane. Their trivializations have exactly the domains of `cutChart` and
`upperChart`. On the left component of the overlap the transition is
`upperExponent`, respectively `upperTangent`; on the right it is the identity.
The projection forgetting the smoothing exponent commutes with every transition.
Thus it gives a continuous map of the lattice bundles, with the prescribed
projection in both chart frames.

The construction uses `TauCeti.fiberBundleCoreOfGroupCocycle` and Mathlib's
`FiberBundleCore` for the total-space topology and local trivializations. The
exponent and tangent shears are those of Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open Set Topology Bundle

private def latticeChart (i : Bool) : OpenPartialHomeomorph regularLocus (ℝ × ℝ) :=
  if i then upperChart else cutChart

open Classical in
private def latticeIndex (p : regularLocus) : Bool :=
  if p ∈ cutChart.source then false else true

private theorem mem_latticeChart_index (p : regularLocus) :
    p ∈ (latticeChart (latticeIndex p)).source := by
  simp only [latticeIndex]
  split_ifs with hp
  · exact hp
  · exact (chart_sources_cover p).resolve_left hp

private def latticeTransition {F : Type*} [AddCommGroup F]
    (e : F ≃+ F) (i j : Bool) (p : regularLocus) : F ≃+ F :=
  if i = j then AddEquiv.refl F else
    if p.val.1 < 0 then if j then e else e.symm else AddEquiv.refl F

private theorem latticeTransition_comp {F : Type*} [AddCommGroup F]
    (e : F ≃+ F) (i j k : Bool) (p : regularLocus) (q : F) :
    latticeTransition e j k p (latticeTransition e i j p q) =
      latticeTransition e i k p q := by
  cases i <;> cases j <;> cases k <;>
    by_cases hp : p.val.1 < 0 <;> simp [latticeTransition, hp]

private theorem continuousOn_latticeTransition {F : Type*} [AddCommGroup F]
    [TopologicalSpace (Equiv.Perm F)] (e : F ≃+ F) (i j : Bool) :
    ContinuousOn (fun p => (latticeTransition e i j p).toEquiv)
      ((latticeChart i).source ∩ (latticeChart j).source) := by
  by_cases hij : i = j
  · subst j
    simpa only [latticeTransition, ↓reduceIte] using continuousOn_const
  intro p hp
  have hx : p.val.1 ≠ 0 := by
    intro hx
    cases i <;> cases j <;> simp_all [latticeChart]
    all_goals linarith
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hn : ∀ᶠ w : regularLocus in 𝓝 p, w.val.1 < 0 :=
      (isOpen_lt continuous_subtype_val.fst continuous_const).mem_nhds hx
    exact ((continuousAt_const (y := (if j then e else e.symm).toEquiv)).congr_of_eventuallyEq
      (hn.mono fun w hw => by simp [latticeTransition, hij, hw])).continuousWithinAt
  · have hn : ∀ᶠ w : regularLocus in 𝓝 p, 0 < w.val.1 :=
      (isOpen_lt continuous_const continuous_subtype_val.fst).mem_nhds hx
    exact ((continuousAt_const (y := (AddEquiv.refl F).toEquiv)).congr_of_eventuallyEq
      (hn.mono fun w hw => by simp [latticeTransition, hij, not_lt.mpr hw.le])).continuousWithinAt

private def latticeBundleCore {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] (e : F ≃+ F) :
    FiberBundleCore Bool regularLocus F := by
  letI : TopologicalSpace (Equiv.Perm F) := ⊥
  letI : DiscreteTopology (Equiv.Perm F) := ⟨rfl⟩
  letI : ContinuousSMul (Equiv.Perm F) F := ⟨continuous_of_discreteTopology⟩
  exact TauCeti.fiberBundleCoreOfGroupCocycle
    (fun i => (latticeChart i).source) (fun i j p => (latticeTransition e i j p).toEquiv)
    (fun i j k p _ => Equiv.ext (latticeTransition_comp e i j k p))
    F (fun i => (latticeChart i).open_source) latticeIndex mem_latticeChart_index
    (continuousOn_latticeTransition e)

private theorem latticeBundleCore_baseSet {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] (e : F ≃+ F) (i : Bool) :
    (latticeBundleCore e).baseSet i = (latticeChart i).source := by
  rw [FiberBundleCore.baseSet_at, latticeBundleCore,
    TauCeti.fiberBundleCoreOfGroupCocycle_localTriv_baseSet]

private theorem latticeBundleCore_indexAt {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] (e : F ≃+ F) (p : regularLocus) :
    (latticeBundleCore e).indexAt p = latticeIndex p := by
  simp only [latticeBundleCore, TauCeti.fiberBundleCoreOfGroupCocycle_indexAt]

private theorem latticeBundleCore_coordChange {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] (e : F ≃+ F) (i j : Bool) (p : regularLocus) (q : F) :
    (latticeBundleCore e).coordChange i j p q = latticeTransition e i j p q := by
  rw [latticeBundleCore, TauCeti.fiberBundleCoreOfGroupCocycle_coordChange]
  rfl

/-- The rank-three exponent lattice local system, in the cut (`false`) and
upper (`true`) frames of the focus-focus atlas. -/
def exponentBundleCore : FiberBundleCore Bool regularLocus (ℤ × ℤ × ℤ) :=
  latticeBundleCore upperExponent.toAddEquiv

/-- The rank-two integral tangent lattice local system of the same atlas. -/
def tangentLatticeBundleCore : FiberBundleCore Bool regularLocus (ℤ × ℤ) :=
  latticeBundleCore upperTangent.toAddEquiv

instance (p : regularLocus) : AddCommGroup (exponentBundleCore.Fiber p) :=
  inferInstanceAs (AddCommGroup (ℤ × ℤ × ℤ))

instance (p : regularLocus) : Module ℤ (exponentBundleCore.Fiber p) :=
  inferInstanceAs (Module ℤ (ℤ × ℤ × ℤ))

instance (p : regularLocus) : AddCommGroup (tangentLatticeBundleCore.Fiber p) :=
  inferInstanceAs (AddCommGroup (ℤ × ℤ))

instance (p : regularLocus) : Module ℤ (tangentLatticeBundleCore.Fiber p) :=
  inferInstanceAs (Module ℤ (ℤ × ℤ))

instance (p : regularLocus) : Module.Free ℤ (exponentBundleCore.Fiber p) :=
  inferInstanceAs (Module.Free ℤ (ℤ × ℤ × ℤ))

instance (p : regularLocus) : Module.Finite ℤ (exponentBundleCore.Fiber p) :=
  inferInstanceAs (Module.Finite ℤ (ℤ × ℤ × ℤ))

instance (p : regularLocus) : Module.Free ℤ (tangentLatticeBundleCore.Fiber p) :=
  inferInstanceAs (Module.Free ℤ (ℤ × ℤ))

instance (p : regularLocus) : Module.Finite ℤ (tangentLatticeBundleCore.Fiber p) :=
  inferInstanceAs (Module.Finite ℤ (ℤ × ℤ))

/-- The exponent trivializations are integral linear on fibers. -/
instance exponentBundleCore_localTriv_isLinear (i : Bool) :
    (exponentBundleCore.localTriv i).IsLinear ℤ where
  linear p _ := by
    have he : (fun q : exponentBundleCore.Fiber p =>
        (exponentBundleCore.localTriv i ⟨p, q⟩).2) =
        fun q => latticeTransition upperExponent.toAddEquiv
          (exponentBundleCore.indexAt p) i p q := by
      funext q
      rw [FiberBundleCore.localTriv_apply]
      exact latticeBundleCore_coordChange _ _ _ _ _
    rw [he]
    exact (latticeTransition upperExponent.toAddEquiv _ _ p).toIntLinearEquiv.isLinear

/-- The tangent trivializations are integral linear on fibers. -/
instance tangentLatticeBundleCore_localTriv_isLinear (i : Bool) :
    (tangentLatticeBundleCore.localTriv i).IsLinear ℤ where
  linear p _ := by
    have he : (fun q : tangentLatticeBundleCore.Fiber p =>
        (tangentLatticeBundleCore.localTriv i ⟨p, q⟩).2) =
        fun q => latticeTransition upperTangent.toAddEquiv
          (tangentLatticeBundleCore.indexAt p) i p q := by
      funext q
      rw [FiberBundleCore.localTriv_apply]
      exact latticeBundleCore_coordChange _ _ _ _ _
    rw [he]
    exact (latticeTransition upperTangent.toAddEquiv _ _ p).toIntLinearEquiv.isLinear

/-- The cut-frame exponent trivialization has the cut chart's source. -/
@[simp] theorem exponentBundleCore_localTriv_baseSet_false :
    (exponentBundleCore.localTriv false).baseSet = cutChart.source := by
  rw [← FiberBundleCore.baseSet_at]
  exact latticeBundleCore_baseSet _ _

/-- The upper-frame exponent trivialization has the upper chart's source. -/
@[simp] theorem exponentBundleCore_localTriv_baseSet_true :
    (exponentBundleCore.localTriv true).baseSet = upperChart.source := by
  rw [← FiberBundleCore.baseSet_at]
  exact latticeBundleCore_baseSet _ _

@[simp] theorem tangentLatticeBundleCore_localTriv_baseSet_false :
    (tangentLatticeBundleCore.localTriv false).baseSet = cutChart.source := by
  rw [← FiberBundleCore.baseSet_at]
  exact latticeBundleCore_baseSet _ _

@[simp] theorem tangentLatticeBundleCore_localTriv_baseSet_true :
    (tangentLatticeBundleCore.localTriv true).baseSet = upperChart.source := by
  rw [← FiberBundleCore.baseSet_at]
  exact latticeBundleCore_baseSet _ _

private theorem exponentBundleCore_indexAt (p : regularLocus) :
    exponentBundleCore.indexAt p = tangentLatticeBundleCore.indexAt p := by
  simp only [exponentBundleCore, tangentLatticeBundleCore, latticeBundleCore_indexAt]

/-- Exponent coordinate changes, including their inverses, in the two frames. -/
theorem exponentBundleCore_coordChange (i j : Bool) (p : regularLocus) (q : ℤ × ℤ × ℤ) :
    exponentBundleCore.coordChange i j p q =
      if i = j then q else if p.val.1 < 0 then
        if j then upperExponent q else upperExponent.symm q else q := by
  rw [exponentBundleCore, latticeBundleCore_coordChange]
  simp only [latticeTransition]
  split_ifs <;> rfl

/-- Tangent coordinate changes are the integral linear parts of the atlas
transitions: the upper shear on the left overlap and the identity on the right. -/
theorem tangentLatticeBundleCore_coordChange (i j : Bool) (p : regularLocus) (q : ℤ × ℤ) :
    tangentLatticeBundleCore.coordChange i j p q =
      if i = j then q else if p.val.1 < 0 then
        if j then upperTangent q else upperTangent.symm q else q := by
  rw [tangentLatticeBundleCore, latticeBundleCore_coordChange]
  simp only [latticeTransition]
  split_ifs <;> rfl

/-- The changes between the actual exponent trivializations are the specified
core transitions. -/
@[simp] theorem exponentBundleCore_localTriv_coordChange (i j : Bool) (p : regularLocus)
    (hp : p ∈ exponentBundleCore.baseSet i ∩ exponentBundleCore.baseSet j) (q : ℤ × ℤ × ℤ) :
    (exponentBundleCore.localTriv i).coordChange (exponentBundleCore.localTriv j) p q =
      exponentBundleCore.coordChange i j p q := by
  let : TopologicalSpace (Equiv.Perm (ℤ × ℤ × ℤ)) := ⊥
  let : DiscreteTopology (Equiv.Perm (ℤ × ℤ × ℤ)) := ⟨rfl⟩
  let : ContinuousSMul (Equiv.Perm (ℤ × ℤ × ℤ)) (ℤ × ℤ × ℤ) :=
    ⟨continuous_of_discreteTopology⟩
  rw [exponentBundleCore, latticeBundleCore_baseSet, latticeBundleCore_baseSet] at hp
  simp only [exponentBundleCore, latticeBundleCore,
    TauCeti.fiberBundleCoreOfGroupCocycle_coordChange]
  exact TauCeti.fiberBundleCoreOfGroupCocycle_localTriv_coordChange
    _ _ _ _ _ _ _ _ i j hp q

/-- The changes between the integral tangent trivializations are the specified
core transitions. -/
@[simp] theorem tangentLatticeBundleCore_localTriv_coordChange (i j : Bool) (p : regularLocus)
    (hp : p ∈ tangentLatticeBundleCore.baseSet i ∩ tangentLatticeBundleCore.baseSet j) (q : ℤ × ℤ) :
    (tangentLatticeBundleCore.localTriv i).coordChange (tangentLatticeBundleCore.localTriv j) p q =
      tangentLatticeBundleCore.coordChange i j p q := by
  let : TopologicalSpace (Equiv.Perm (ℤ × ℤ)) := ⊥
  let : DiscreteTopology (Equiv.Perm (ℤ × ℤ)) := ⟨rfl⟩
  let : ContinuousSMul (Equiv.Perm (ℤ × ℤ)) (ℤ × ℤ) := ⟨continuous_of_discreteTopology⟩
  rw [tangentLatticeBundleCore, latticeBundleCore_baseSet, latticeBundleCore_baseSet] at hp
  simp only [tangentLatticeBundleCore, latticeBundleCore,
    TauCeti.fiberBundleCoreOfGroupCocycle_coordChange]
  exact TauCeti.fiberBundleCoreOfGroupCocycle_localTriv_coordChange
    _ _ _ _ _ _ _ _ i j hp q

/-- The coefficient exponent monoid is preserved in both directions by every
change of lattice frame. -/
@[simp↓] theorem exponentBundleCore_coordChange_mem_exponentMonoid
    (i j : Bool) (p : regularLocus) (q : ℤ × ℤ × ℤ) :
    exponentBundleCore.coordChange i j p q ∈ exponentMonoid ↔ q ∈ exponentMonoid := by
  rw [exponentBundleCore_coordChange]
  split_ifs <;> simp

/-- Projection to spatial degree intertwines every change of lattice frames. -/
theorem exponentProjection_coordChange (i j : Bool) (p : regularLocus) (q : ℤ × ℤ × ℤ) :
    exponentProjection (exponentBundleCore.coordChange i j p q) =
      tangentLatticeBundleCore.coordChange i j p (exponentProjection q) := by
  rw [exponentBundleCore_coordChange, tangentLatticeBundleCore_coordChange]
  split_ifs <;> simp

/-- Forget the smoothing exponent in the preferred frame. Compatibility with
coordinate changes makes this a map of lattice local systems. -/
def latticeProjection : exponentBundleCore.TotalSpace → tangentLatticeBundleCore.TotalSpace :=
  fun z => ⟨z.proj, exponentProjection z.2⟩

/-- The lattice projection lies over the identity of the punctured plane. -/
@[simp] theorem latticeProjection_proj (z : exponentBundleCore.TotalSpace) :
    (latticeProjection z).proj = z.proj := (rfl)

/-- On a preferred-frame representative the projection forgets precisely
the smoothing coordinate. -/
@[simp] theorem latticeProjection_mk (p : regularLocus) (q : ℤ × ℤ × ℤ) :
    latticeProjection ⟨p, q⟩ = ⟨p, exponentProjection q⟩ := (rfl)

/-- In either atlas trivialization, the bundle map is the original exponent
projection. This formula also characterizes its effect on local sections. -/
@[simp↓] theorem latticeProjection_localTriv (i : Bool) (z : exponentBundleCore.TotalSpace) :
    (tangentLatticeBundleCore.localTriv i (latticeProjection z)).2 =
      exponentProjection ((exponentBundleCore.localTriv i z).2) := by
  simp only [FiberBundleCore.localTriv_apply, latticeProjection, exponentBundleCore_indexAt]
  exact (exponentProjection_coordChange _ _ _ _).symm

/-- The spatial projection is continuous for the glued bundle topologies. -/
@[continuity] theorem continuous_latticeProjection : Continuous latticeProjection := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := exponentBundleCore.indexAt z.proj
  have hz : z ∈ (exponentBundleCore.localTriv i).source :=
    exponentBundleCore.mem_baseSet_at z.proj
  -- Both cores have the same chart domains and preferred index, so this source
  -- is also the preimage of the target trivialization's source.
  have hn : latticeProjection ⁻¹' (tangentLatticeBundleCore.localTriv i).source ∈ 𝓝 z :=
    by
      convert (exponentBundleCore.localTriv i).open_source.mem_nhds hz using 1
      ext w
      simp only [mem_preimage, Trivialization.mem_source,
        latticeProjection_proj]
      cases i <;> simp only [exponentBundleCore_localTriv_baseSet_false,
        exponentBundleCore_localTriv_baseSet_true, tangentLatticeBundleCore_localTriv_baseSet_false,
        tangentLatticeBundleCore_localTriv_baseSet_true]
  let e := (tangentLatticeBundleCore.localTriv i).toOpenPartialHomeomorph
  apply (e.continuousAt_iff_continuousAt_comp_left hn).mpr
  have hc := (exponentBundleCore.localTriv i).continuousAt hz
  have hp : Continuous (exponentProjection : (ℤ × ℤ × ℤ) → ℤ × ℤ) :=
    continuous_of_discreteTopology
  convert (exponentBundleCore.continuous_proj.continuousAt.prodMk
    (hp.continuousAt.comp hc.snd)) using 1
  funext w
  apply Prod.ext
  · rfl
  · exact latticeProjection_localTriv i w

end Mei.FocusFocus
