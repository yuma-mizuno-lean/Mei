/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mei.Topology.LocallyConstant.Extend

/-!
# Transport sheaves with coefficients on a dense subset

Transport between points of a dense subset, specified coherently on basis opens,
defines a sheaf on the whole space. Its sections have values only on the dense
subset: no arbitrary values are attached to the missing points. Local parallelness
nevertheless imposes compatibility across those points. Normalizing in a transport
chart gives a locally constant function on the whole chart, so evaluation at any
dense point identifies sections on preconnected subopens with the coefficient type.

This is the dense-domain version of `BasisTransport.sheaf`. We use Mathlib's
`PrelocalPredicate.sheafify` and `subsheafToTypes`, and
`LocallyConstant.extendOfDenseRange` for normalized coefficients.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Filter Topology TopCat

universe u v

namespace Mei

variable {X : TopCat.{u}} (S : Set X) (M : Type v)

/-- Coherent local transport on a dense subset. Missing points carry no coefficient
values, but the basis opens belong to the whole ambient space. -/
@[ext]
structure DenseBasisTransport where
  /-- The coefficient domain is dense. -/
  dense : Dense S
  /-- Opens on which transport is specified. -/
  basis : Set (Opens X)
  /-- Transport charts form an ambient basis. -/
  isBasis : Opens.IsBasis basis
  /-- Transport between coefficient points in one chart. -/
  transport : ∀ U, U ∈ basis → ∀ x y : S, x.val ∈ U → y.val ∈ U → M ≃ M
  /-- Transport composes in traversal order. -/
  transport_trans : ∀ U hU x y z hx hy hz,
    (transport U hU x y hx hy).trans (transport U hU y z hy hz) =
      transport U hU x z hx hz
  /-- Inclusions of charts preserve transport. -/
  transport_restrict : ∀ {U V} (hU : U ∈ basis) (hV : V ∈ basis)
    (hUV : U ≤ V) x y hx hy,
    transport U hU x y hx hy = transport V hV x y (hUV hx) (hUV hy)

namespace DenseBasisTransport

variable {S M} (T : DenseBasisTransport S M)

/-- The cocycle forces identity transport at every coefficient point. -/
@[simp]
theorem transport_self (U) (hU : U ∈ T.basis) (x : S) (hx : x.val ∈ U) :
    T.transport U hU x x hx hx = Equiv.refl M := by
  ext a
  apply (T.transport U hU x x hx hx).injective
  exact congrArg (fun e => e a) (T.transport_trans U hU x x x hx hx hx)

/-- Parallelness on every transport chart contained in the domain. The fiber at
a missing point is an empty-domain function and hence carries no free data. -/
def prelocal : PrelocalPredicate (fun x : X => x ∈ S → M) where
  pred {U} f := ∀ V (hV : V ∈ T.basis) (hVU : V ≤ U) (x y : S)
    (hx : x.val ∈ V) (hy : y.val ∈ V),
    T.transport V hV x y hx hy (f ⟨x.val, hVU hx⟩ x.property) =
      f ⟨y.val, hVU hy⟩ y.property
  res i _ hf V hV hVU x y hx hy := hf V hV (hVU.trans i.le) x y hx hy

/-- The prelocal condition is exactly parallelness on contained charts. -/
@[simp]
theorem prelocal_pred_iff {U : Opens X} (f : ∀ x : U, x.val ∈ S → M) :
    T.prelocal.pred f ↔ ∀ V (hV : V ∈ T.basis) (hVU : V ≤ U) (x y : S)
      (hx : x.val ∈ V) (hy : y.val ∈ V),
      T.transport V hV x y hx hy (f ⟨x.val, hVU hx⟩ x.property) =
        f ⟨y.val, hVU hy⟩ y.property := Iff.rfl

/-- The ambient sheaf of locally parallel coefficients on the dense subset. -/
def sheaf : X.Sheaf (Type (max u v)) := subsheafToTypes T.prelocal.sheafify

/-- Evaluate a section at a coefficient point of its domain. -/
def value {U : Opens X} (s : T.sheaf.presheaf.obj (op U))
    (x : S) (hx : x.val ∈ U) : M := s.val ⟨x.val, hx⟩ x.property

/-- Construct a section from locally parallel coefficient functions. -/
def sectionOfLocallyParallel {U : Opens X} (f : ∀ x : U, x.val ∈ S → M)
    (hf : T.prelocal.sheafify.pred f) : T.sheaf.presheaf.obj (op U) := ⟨f, hf⟩

/-- A constructed section has the prescribed coefficient values. -/
@[simp]
theorem value_sectionOfLocallyParallel {U : Opens X} (f : ∀ x : U, x.val ∈ S → M)
    (hf : T.prelocal.sheafify.pred f) (x : S) (hx : x.val ∈ U) :
    T.value (T.sectionOfLocallyParallel f hf) x hx = f ⟨x.val, hx⟩ x.property := (rfl)

/-- The coefficient function of every section is locally parallel. -/
theorem locallyParallel_value {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) :
    T.prelocal.sheafify.pred (fun x hx => T.value s ⟨x.val, hx⟩ x.property) := s.property

/-- Values at coefficient points determine the section, including across the
complement of the dense subset. -/
@[ext]
theorem section_ext {U : Opens X} {s t : T.sheaf.presheaf.obj (op U)}
    (h : ∀ x hx, T.value s x hx = T.value t x hx) : s = t := by
  apply Subtype.ext
  funext x hx
  exact h ⟨x.val, hx⟩ x.property

/-- Reconstructing a section from its coefficient function recovers it. -/
@[simp]
theorem sectionOfLocallyParallel_value {U : Opens X}
    (s : T.sheaf.presheaf.obj (op U)) :
    T.sectionOfLocallyParallel (fun x hx => T.value s ⟨x.val, hx⟩ x.property)
      (T.locallyParallel_value s) = s := by
  apply T.section_ext
  intro x hx
  rfl

/-- Restriction preserves all coefficient values in the smaller open. -/
@[simp]
theorem value_restrict {U V : Opens X} (hVU : V ≤ U)
    (s : T.sheaf.presheaf.obj (op U)) (x : S) (hx : x.val ∈ V) :
    T.value (T.sheaf.presheaf.map (homOfLE hVU).op s) x hx =
      T.value s x (hVU hx) := (rfl)

/-- Transporting a coefficient from a fixed chart point gives a section on
every subopen of that chart. -/
def parallelSection {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    (x : S) (hx : x.val ∈ B) (a : M) : T.sheaf.presheaf.obj (op U) :=
  ⟨fun y hy => T.transport B hB x ⟨y.val, hy⟩ hx (hUB y.property) a,
    PrelocalPredicate.sheafifyOf (by
      intro V hV hVU y z hy hz
      rw [T.transport_restrict hV hB (hVU.trans hUB)]
      exact congrArg (fun e => e a) (T.transport_trans B hB x y z hx
        (hUB (hVU hy)) (hUB (hVU hz))))⟩

/-- The parallel section has precisely the transported coefficient values. -/
@[simp]
theorem value_parallelSection {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    (x : S) (hx : x.val ∈ B) (a : M) (y : S) (hy : y.val ∈ U) :
    T.value (T.parallelSection hB hUB x hx a) y hy =
      T.transport B hB x y hx (hUB hy) a := (rfl)

/-- Normalized values extend locally constantly across all missing points
of a chart. This is stronger than local constancy on the dense domain alone. -/
theorem exists_normalized {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    (a : S) (ha : a.val ∈ B) (s : T.sheaf.presheaf.obj (op U)) :
    ∃ g : LocallyConstant U M, ∀ (x : S) (hx : x.val ∈ U),
      g ⟨x.val, hx⟩ = T.transport B hB x a (hUB hx) ha (T.value s x hx) := by
  let A := {x : S // x.val ∈ U}
  let f : A → U := (U : Set X).restrictPreimage (Subtype.val : S → X)
  have hd : DenseRange f := by
    have hdU : Dense (((↑) : U → X) ⁻¹' S) :=
      T.dense.preimage U.isOpen.isOpenMap_subtype_val
    have hr : range f = ((↑) : U → X) ⁻¹' S := by
      rw [Set.range_restrictPreimage, Subtype.range_coe_subtype]
      -- The open and its underlying set have the same subtype projection.
      rfl
    -- Express density using the range of the two nested subtype projections.
    simpa only [DenseRange, hr] using hdU
  let g : A → M := fun x =>
    T.transport B hB x.val a (hUB x.property) ha (T.value s x.val x.property)
  have hg : ∀ x : U, ∃ m : M, ∀ᶠ y in comap f (𝓝 x), g y = m := by
    intro x
    obtain ⟨W, hxW, i, hsW⟩ := s.property x
    obtain ⟨C, hC, hxC, hCW⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis hxW
    have hCU : C ≤ U := hCW.trans i.le
    obtain ⟨z, hzC, hzS⟩ := T.dense.inter_open_nonempty C C.isOpen ⟨x.val, hxC⟩
    let z' : S := ⟨z, hzS⟩
    refine ⟨T.transport B hB z' a (hUB (hCU hzC)) ha
      (T.value s z' (hCU hzC)), ?_⟩
    have hn : ∀ᶠ y : U in 𝓝 x, y.val ∈ C :=
      (C.isOpen.preimage continuous_subtype_val).mem_nhds hxC
    filter_upwards [hn.comap f] with y hy
    simp only [f, Set.restrictPreimage_coe] at hy
    have hp := hsW C hC hCW z' y.val hzC hy
    rw [T.transport_restrict hC hB (hCU.trans hUB)] at hp
    have hp' : T.transport B hB z' y.val (hUB (hCU hzC)) (hUB y.property)
        (T.value s z' (hCU hzC)) = T.value s y.val y.property := hp
    dsimp only [g]
    rw [← hp']
    exact congrArg (fun e => e (T.value s z' (hCU hzC)))
      (T.transport_trans B hB z' y.val a (hUB (hCU hzC)) (hUB y.property) ha)
  refine ⟨LocallyConstant.extendOfDenseRange f hd g hg, fun x hx => ?_⟩
  exact LocallyConstant.extendOfDenseRange_apply f hd g hg ⟨x, hx⟩

/-- On a preconnected subopen of a transport chart, every section satisfies
the transport equation between every two coefficient points. -/
theorem parallel_of_le {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (s : T.sheaf.presheaf.obj (op U))
    (x y : S) (hx : x.val ∈ U) (hy : y.val ∈ U) :
    T.transport B hB x y (hUB hx) (hUB hy) (T.value s x hx) = T.value s y hy := by
  obtain ⟨g, hg⟩ := T.exists_normalized hB hUB y (hUB hy) s
  have he : g (⟨x.val, hx⟩ : U) = g ⟨y.val, hy⟩ :=
    g.isLocallyConstant.apply_eq_of_preconnectedSpace
    (⟨x.val, hx⟩ : U) ⟨y.val, hy⟩
  rw [hg x hx, hg y hy] at he
  simpa only [T.transport_self, Equiv.refl_apply] using he

/-- Evaluation identifies sections on a preconnected subopen of a chart with
the coefficient type. The point may be any dense-domain point in that subopen. -/
def evaluationEquiv {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U) :
    T.sheaf.presheaf.obj (op U) ≃ M where
  toFun s := T.value s x hx
  invFun a := T.parallelSection hB hUB x (hUB hx) a
  left_inv s := T.section_ext (fun y hy => by
    simpa only [value_parallelSection] using T.parallel_of_le hB hUB s x y hx hy)
  right_inv a := by simp

/-- The evaluation equivalence evaluates actual coefficients. -/
@[simp]
theorem evaluationEquiv_apply {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.evaluationEquiv hB hUB x hx s = T.value s x hx := (rfl)

/-- Inverse evaluation reconstructs every coefficient by transport. -/
@[simp]
theorem value_evaluationEquiv_symm {B U : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    [PreconnectedSpace U] (x : S) (hx : x.val ∈ U) (a : M) (y : S) (hy : y.val ∈ U) :
    T.value ((T.evaluationEquiv hB hUB x hx).symm a) y hy =
      T.transport B hB x y (hUB hx) (hUB hy) a := (rfl)

/-- Restrictions between nonempty preconnected subopens of one chart are bijective. -/
theorem restriction_bijective {B U V : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    (hcU : IsPreconnected (U : Set X)) (hVU : V ≤ U)
    (hne : (V : Set X).Nonempty) (hcV : IsPreconnected (V : Set X)) :
    Function.Bijective (T.sheaf.presheaf.map (homOfLE hVU).op) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hcU
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hcV
  obtain ⟨x, hxV, hxS⟩ := T.dense.inter_open_nonempty V V.isOpen hne
  let x' : S := ⟨x, hxS⟩
  constructor
  · intro s t he
    apply (T.evaluationEquiv hB hUB x' (hVU hxV)).injective
    simpa only [evaluationEquiv_apply, value_restrict] using
      congrArg (fun r => T.value r x' hxV) he
  · intro t
    refine ⟨(T.evaluationEquiv hB hUB x' (hVU hxV)).symm (T.value t x' hxV), ?_⟩
    apply (T.evaluationEquiv hB (hVU.trans hUB) x' hxV).injective
    simp

end DenseBasisTransport
end Mei
