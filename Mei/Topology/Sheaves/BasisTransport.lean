/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.LocallyConstant
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sheaves from coherent transport on a basis

Equivalences between fibers on basis opens, satisfying the cocycle law and
compatible with restriction, define a sheaf of locally parallel functions.
We use Mathlib's `PrelocalPredicate.sheafify` and `subsheafToTypes`, so gluing
is inherited from its existing sheaf of dependent functions. No global
transport or global trivialization is assumed; different chains of basis
opens may have monodromy.
-/

public section

open CategoryTheory TopologicalSpace Opposite Set Filter Topology TopCat

universe u v

namespace Mei

variable {X : TopCat.{u}} (E : X → Type v)

/-- Coherent fiber equivalences on a topological basis, with compatibility on
inclusions of basis opens. No connectedness or constant-fiber hypothesis is needed. -/
structure BasisTransport where
  /-- The opens carrying specified transport. -/
  basis : Set (Opens X)
  /-- The specified opens form a basis. -/
  isBasis : Opens.IsBasis basis
  /-- Parallel transport between points of a basis open. -/
  transport : ∀ (U : Opens X), U ∈ basis → (x y : U) → E x ≃ E y
  /-- Transport satisfies the local cocycle law. -/
  transport_trans : ∀ (U) (hU : U ∈ basis) (x y z : U),
    (transport U hU x y).trans (transport U hU y z) = transport U hU x z
  /-- Restricting a basis chart preserves its specified transport. -/
  transport_restrict : ∀ {U V} (hU : U ∈ basis) (hV : V ∈ basis) (hUV : U ≤ V) (x y : U),
    transport U hU x y = transport V hV ⟨x, hUV x.property⟩ ⟨y, hUV y.property⟩

namespace BasisTransport

variable {E} (T : BasisTransport E)

/-- The cocycle law forces transport at a point to be the identity. -/
@[simp]
theorem transport_self (U) (hU : U ∈ T.basis) (x : U) :
    T.transport U hU x x = Equiv.refl _ := by
  ext a
  apply (T.transport U hU x x).injective
  exact congrArg (fun e => e a) (T.transport_trans U hU x x x)

/-- Successive transports compute as a single local transport. -/
@[simp]
theorem transport_trans_apply (U) (hU : U ∈ T.basis) (x y z : U) (a : E x) :
    T.transport U hU y z (T.transport U hU x y a) = T.transport U hU x z a :=
  congrArg (fun e => e a) (T.transport_trans U hU x y z)

/-- Functions parallel on each basis open contained in their domain.
Restriction preserves this predicate; sheafification makes the condition local. -/
def prelocal : PrelocalPredicate E where
  pred {U} f := ∀ (V : Opens X) (hV : V ∈ T.basis) (hVU : V ≤ U) (x y : V),
    T.transport V hV x y (f ⟨x, hVU x.property⟩) = f ⟨y, hVU y.property⟩
  res i _ hf V hV hVU x y := hf V hV (hVU.trans i.le) x y

/-- The prelocal predicate is exactly parallelness on all contained basis opens. -/
@[simp]
theorem prelocal_pred_iff {U : Opens X} (f : ∀ x : U, E x) :
    T.prelocal.pred f ↔ ∀ (V : Opens X) (hV : V ∈ T.basis) (hVU : V ≤ U) (x y : V),
      T.transport V hV x y (f ⟨x, hVU x.property⟩) = f ⟨y, hVU y.property⟩ := Iff.rfl

/-- Transporting one fiber value over a chart gives a parallel function on each subopen. -/
theorem prelocal_transport {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    (x : U) (a : E x) :
    T.prelocal.pred (fun y : V => T.transport U hU x ⟨y, hVU y.property⟩ a) := by
  rw [prelocal_pred_iff]
  intro W hW hWV y z
  calc
    T.transport W hW y z (T.transport U hU x ⟨y, hVU (hWV y.property)⟩ a) =
        T.transport U hU ⟨y, hVU (hWV y.property)⟩ ⟨z, hVU (hWV z.property)⟩
          (T.transport U hU x ⟨y, hVU (hWV y.property)⟩ a) :=
      congrArg (fun e => e (T.transport U hU x ⟨y, hVU (hWV y.property)⟩ a))
        (T.transport_restrict hW hU (hWV.trans hVU) y z)
    _ = T.transport U hU x ⟨z, hVU (hWV z.property)⟩ a :=
      T.transport_trans_apply U hU _ _ _ _

/-- Locally parallel functions form a sheaf, using Mathlib's local-predicate constructor.
The public section API characterizes its values and local parallelness. -/
noncomputable def sheaf : X.Sheaf (Type (max u v)) :=
  subsheafToTypes T.prelocal.sheafify

/-- The value of a locally parallel section in the specified fiber. -/
noncomputable def value {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) (x : U) : E x := s.val x

/-- Sections are determined by their values in every point fiber. -/
@[ext]
theorem ext {U : Opens X} {s t : T.sheaf.presheaf.obj (op U)}
    (h : ∀ x, T.value s x = T.value t x) : s = t :=
  Subtype.ext (funext h)

/-- Construct a section from a locally parallel dependent function. This does
not require parallelness on disconnected basis opens outside the local witnesses. -/
noncomputable def sectionOfLocallyParallel {U : Opens X} (f : ∀ x : U, E x)
    (hf : T.prelocal.sheafify.pred f) : T.sheaf.presheaf.obj (op U) := ⟨f, hf⟩

/-- A constructed locally parallel section has the specified point values. -/
@[simp]
theorem value_sectionOfLocallyParallel {U : Opens X} (f : ∀ x : U, E x)
    (hf : T.prelocal.sheafify.pred f) (x : U) :
    T.value (T.sectionOfLocallyParallel f hf) x = f x := (rfl)

/-- Every section is locally parallel in the supplied transport charts. -/
theorem locallyParallel_value {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) :
    T.prelocal.sheafify.pred (T.value s) := s.property

/-- A dependent function is the value function of a section exactly when it is
locally parallel. -/
theorem exists_section_value_iff {U : Opens X} (f : ∀ x : U, E x) :
    (∃ s : T.sheaf.presheaf.obj (op U), T.value s = f) ↔ T.prelocal.sheafify.pred f := by
  constructor
  · rintro ⟨s, rfl⟩
    exact T.locallyParallel_value s
  · intro hf
    exact ⟨T.sectionOfLocallyParallel f hf, rfl⟩

/-- Reconstructing a section from its locally parallel value function recovers it. -/
@[simp]
theorem sectionOfLocallyParallel_value {U : Opens X} (s : T.sheaf.presheaf.obj (op U)) :
    T.sectionOfLocallyParallel (T.value s) (T.locallyParallel_value s) = s := by
  apply T.ext
  intro x
  rfl

/-- A function parallel on all contained basis opens gives a locally parallel section. -/
noncomputable def sectionOfParallel {U : Opens X} (f : ∀ x : U, E x)
    (hf : T.prelocal.pred f) : T.sheaf.presheaf.obj (op U) :=
  T.sectionOfLocallyParallel f (PrelocalPredicate.sheafifyOf hf)

/-- Constructed sections retain their specified function values. -/
@[simp]
theorem value_sectionOfParallel {U : Opens X} (f : ∀ x : U, E x)
    (hf : T.prelocal.pred f) (x : U) : T.value (T.sectionOfParallel f hf) x = f x := (rfl)

/-- A section parallel on every contained basis open is also recovered by the
stronger parallel-function constructor. -/
@[simp]
theorem sectionOfParallel_value {U : Opens X} (s : T.sheaf.presheaf.obj (op U))
    (hf : T.prelocal.pred (T.value s)) : T.sectionOfParallel (T.value s) hf = s := by
  apply T.ext
  intro x
  rfl

/-- Restriction evaluates by the inclusion of open domains. -/
@[simp]
theorem value_restrict {U V : Opens X} (hVU : V ≤ U)
    (s : T.sheaf.presheaf.obj (op U)) (x : V) :
    T.value (T.sheaf.presheaf.map (homOfLE hVU).op s) x =
      T.value s ⟨x, hVU x.property⟩ := (rfl)

/-- A section, expressed in one basis chart and referenced to a fixed fiber,
is locally constant on any open subdomain of that chart. -/
theorem isLocallyConstant_normalized {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    (a : U) (s : T.sheaf.presheaf.obj (op V)) :
    IsLocallyConstant (fun y : V => T.transport U hU ⟨y, hVU y.property⟩ a (T.value s y)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  obtain ⟨W, hyW, i, hsW⟩ := T.locallyParallel_value s y
  obtain ⟨B, hB, hyB, hBW⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis hyW
  have hBU : B ≤ U := hBW.trans (i.le.trans hVU)
  have hn : ∀ᶠ z : V in 𝓝 y, (z : X) ∈ B :=
    (B.isOpen.preimage continuous_subtypeVal).mem_nhds hyB
  filter_upwards [hn] with z hz
  have h := hsW B hB hBW ⟨y, hyB⟩ ⟨z, hz⟩
  rw [T.transport_restrict hB hU hBU] at h
  calc
    T.transport U hU ⟨z, hVU z.property⟩ a (T.value s z) =
        T.transport U hU ⟨z, hVU z.property⟩ a
          (T.transport U hU ⟨y, hVU y.property⟩ ⟨z, hVU z.property⟩ (T.value s y)) :=
      congrArg (T.transport U hU ⟨z, hVU z.property⟩ a) h.symm
    _ = T.transport U hU ⟨y, hVU y.property⟩ a (T.value s y) :=
      T.transport_trans_apply U hU _ _ _ _

/-- On a preconnected open inside a basis chart, local parallelness implies the
transport equation between any two of its points. -/
theorem parallel_of_le {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    [PreconnectedSpace V] (s : T.sheaf.presheaf.obj (op V)) (x y : V) :
    T.transport U hU ⟨x, hVU x.property⟩ ⟨y, hVU y.property⟩ (T.value s x) =
      T.value s y := by
  have h := IsLocallyConstant.apply_eq_of_preconnectedSpace
    (T.isLocallyConstant_normalized hU hVU ⟨y, hVU y.property⟩ s) x y
  simpa only [transport_self, Equiv.refl_apply] using h

/-- A locally parallel section on a preconnected subopen of one basis chart is
determined uniquely by its value at any chosen point. -/
noncomputable def evaluationEquiv {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    [PreconnectedSpace V] (x : V) : T.sheaf.presheaf.obj (op V) ≃ E x where
  toFun s := T.value s x
  invFun a := T.sectionOfParallel
    (fun y : V => T.transport U hU ⟨x, hVU x.property⟩ ⟨y, hVU y.property⟩ a)
    (T.prelocal_transport hU hVU ⟨x, hVU x.property⟩ a)
  left_inv s := T.ext (fun y => T.parallel_of_le hU hVU s x y)
  right_inv a := by
    dsimp only
    rw [value_sectionOfParallel]
    exact congrArg (fun e => e a) (T.transport_self U hU ⟨x, hVU x.property⟩)

/-- Evaluation of the chartwise equivalence is actual fiber evaluation. -/
@[simp]
theorem evaluationEquiv_apply {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    [PreconnectedSpace V] (x : V) (s : T.sheaf.presheaf.obj (op V)) :
    T.evaluationEquiv hU hVU x s = T.value s x := (rfl)

/-- Reconstructing a section transports its chosen value within the chart. -/
@[simp]
theorem evaluationEquiv_symm_apply {U V : Opens X} (hU : U ∈ T.basis) (hVU : V ≤ U)
    [PreconnectedSpace V] (x y : V) (a : E x) :
    T.value ((T.evaluationEquiv hU hVU x).symm a) y =
      T.transport U hU ⟨x, hVU x.property⟩ ⟨y, hVU y.property⟩ a := (rfl)

/-- Restriction between nonempty preconnected subopens of a single basis chart
is bijective. The subopens need not themselves belong to the supplied basis. -/
theorem restriction_bijective {B U V : Opens X} (hB : B ∈ T.basis) (hUB : U ≤ B)
    (hcU : IsPreconnected (U : Set X)) (hVU : V ≤ U)
    (hne : (V : Set X).Nonempty) (hcV : IsPreconnected (V : Set X)) :
    Function.Bijective (T.sheaf.presheaf.map (homOfLE hVU).op) := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hcU
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hcV
  obtain ⟨x, hx⟩ := hne
  let y : V := ⟨x, hx⟩
  let z : U := ⟨x, hVU hx⟩
  constructor
  · intro s t h
    apply (T.evaluationEquiv hB hUB z).injective
    simpa only [evaluationEquiv_apply, value_restrict] using
      congrArg (fun r => T.value r y) h
  · intro t
    refine ⟨(T.evaluationEquiv hB hUB z).symm (T.value t y), ?_⟩
    apply (T.evaluationEquiv hB (hVU.trans hUB) y).injective
    simp only [evaluationEquiv_apply, value_restrict, evaluationEquiv_symm_apply,
      y, z, transport_self, Equiv.refl_apply]

/-- Coherent transport has locally bijective preconnected restrictions if each
point has a preconnected open neighborhood contained in a basis chart. Neither
these neighborhoods nor their subopens need belong to the supplied basis. -/
theorem hasLocallyBijectivePreconnectedRestrictions
    (hc : ∀ x : X, ∃ B ∈ T.basis, ∃ U : Opens X,
      x ∈ U ∧ U ≤ B ∧ IsPreconnected (U : Set X)) :
    T.sheaf.HasLocallyBijectivePreconnectedRestrictions where
  exists_bijective_restrictions x := by
    obtain ⟨B, hB, U, hxU, hUB, hcU⟩ := hc x
    exact ⟨U, hxU,
      fun V hVU hne hcV => T.restriction_bijective hB hUB hcU hVU hne hcV⟩

end BasisTransport
end Mei
