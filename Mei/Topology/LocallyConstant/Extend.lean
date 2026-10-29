/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.DenseEmbedding

/-!
# Locally constant extension from a dense range

A function on a dense range extends to a locally constant function precisely
when it is constant near every ambient point, including points outside that
range. This is the extension criterion for chart-normalized coefficients on
the complement of walls. Local constancy on the dense domain alone does not
imply extendability across a missing wall.

We reuse Mathlib's `IsDenseInducing.extend` with the topology induced on the
domain and the discrete topology on the coefficient type, and
`DenseRange.equalizer` for uniqueness. Neither a topology on the original
domain or coefficient type nor injectivity of the dense map is required.
-/

public section

open Filter Topology

universe u v w

namespace LocallyConstant

variable {A : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X]
  (f : A → X) (hd : DenseRange f) (g : A → Y)
  (hg : ∀ x : X, ∃ y : Y, ∀ᶠ a in Filter.comap f (𝓝 x), g a = y)

/-- Extend locally constant chart values across a dense range. The hypothesis
requires constancy near every ambient point, not merely near points in the range. -/
noncomputable def extendOfDenseRange : LocallyConstant X Y := by
  let : TopologicalSpace A := TopologicalSpace.induced f inferInstance
  let : TopologicalSpace Y := ⊥
  let : DiscreteTopology Y := ⟨rfl⟩
  let : RegularSpace Y := .of_hasBasis (fun y => nhds_basis_opens y)
    (fun _ _ _ => isClosed_discrete _)
  let hi : IsDenseInducing f := ⟨⟨rfl⟩, hd⟩
  refine ⟨hi.extend g, (IsLocallyConstant.iff_continuous _).mpr ?_⟩
  apply hi.continuous_extend
  intro x
  obtain ⟨y, hy⟩ := hg x
  exact ⟨y, by simpa only [nhds_discrete] using tendsto_pure.mpr hy⟩

/-- The extension recovers all specified values on the dense domain. -/
@[simp]
theorem extendOfDenseRange_apply (a : A) : extendOfDenseRange f hd g hg (f a) = g a := by
  let : TopologicalSpace A := TopologicalSpace.induced f inferInstance
  let : TopologicalSpace Y := ⊥
  let : DiscreteTopology Y := ⟨rfl⟩
  dsimp only [extendOfDenseRange]
  let hi : IsDenseInducing f := ⟨⟨rfl⟩, hd⟩
  apply hi.extend_eq'
  intro x
  obtain ⟨y, hy⟩ := hg x
  exact ⟨y, by simpa only [nhds_discrete] using tendsto_pure.mpr hy⟩

/-- A locally constant function is the extension exactly when its values agree
on the dense domain. This characterizes the unexposed construction. -/
theorem eq_extendOfDenseRange_iff (k : LocallyConstant X Y) :
    k = extendOfDenseRange f hd g hg ↔ ∀ a, k (f a) = g a := by
  constructor
  · rintro rfl a
    exact extendOfDenseRange_apply f hd g hg a
  · intro hk
    let : TopologicalSpace Y := ⊥
    let : DiscreteTopology Y := ⟨rfl⟩
    apply DFunLike.coe_injective
    apply hd.equalizer k.continuous (extendOfDenseRange f hd g hg).continuous
    funext a
    exact (hk a).trans (extendOfDenseRange_apply f hd g hg a).symm

end LocallyConstant

/-- Dense data have a unique locally constant extension if and only if they
are constant near every ambient point. No topology on the dense domain is needed. -/
theorem DenseRange.existsUnique_locallyConstant_extension_iff
    {A : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X]
    {f : A → X} (hd : DenseRange f) (g : A → Y) :
    (∃! k : LocallyConstant X Y, ∀ a, k (f a) = g a) ↔
      ∀ x : X, ∃ y : Y, ∀ᶠ a in Filter.comap f (𝓝 x), g a = y := by
  constructor
  · rintro ⟨k, hk, _⟩ x
    refine ⟨k x, ?_⟩
    have h := (k.isLocallyConstant.eventually_eq x).comap f
    filter_upwards [h] with a ha
    exact (hk a).symm.trans ha
  · intro hg
    refine ⟨LocallyConstant.extendOfDenseRange f hd g hg,
      LocallyConstant.extendOfDenseRange_apply f hd g hg, ?_⟩
    intro k hk
    exact (LocallyConstant.eq_extendOfDenseRange_iff f hd g hg k).mpr hk
