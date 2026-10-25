/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Lifts through injective linear maps and common lifts along spans

A linear map `g : E →ₗ[R] W` factors through an injective linear map `f : N →ₗ[R] W` exactly
when the range of `g` lies in the range of `f` (`LinearMap.exists_comp_eq_iff_range_le`), and
then the factorization is unique. The factorization is Mathlib's `LinearMap.codLift`.

Applied to `f.prod g` for a span `U ← N → V`, this describes *common lifts*: linear maps
`ℓ : E →ₗ[R] N` with `f ∘ₗ ℓ = α` and `g ∘ₗ ℓ = β` for given `α : E →ₗ[R] U` and
`β : E →ₗ[R] V`. When the span is jointly injective, a common lift exists exactly when every
pair `(α e, β e)` lies in the joint range of the span, and it is then unique
(`LinearMap.existsUnique_comp_eq_and_comp_eq_iff`). Coefficient propagation across a face of a
scattering diagram uses such lifts: the face module is identified with the pairs of chamber
coefficients that it relates.
-/

public section

namespace LinearMap

variable {R E N U V W : Type*} [Semiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid N] [Module R N]
  [AddCommMonoid U] [Module R U] [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W]

/-- A linear map factors through an injective linear map exactly when its range is contained in
the range of that map. -/
theorem exists_comp_eq_iff_range_le {f : N →ₗ[R] W} (hf : Function.Injective f)
    {g : E →ₗ[R] W} : (∃ ℓ : E →ₗ[R] N, f ∘ₗ ℓ = g) ↔ range g ≤ range f := by
  refine ⟨?_, fun h => ⟨g.codLift f hf fun e => h ⟨e, rfl⟩, comp_codLift ..⟩⟩
  rintro ⟨ℓ, rfl⟩
  exact range_comp_le_range ℓ f

/-- A pair of maps has a common lift along a span exactly when their product does. -/
theorem prod_comp_eq_prod_iff {f : N →ₗ[R] U} {g : N →ₗ[R] V} {ℓ : E →ₗ[R] N}
    {α : E →ₗ[R] U} {β : E →ₗ[R] V} :
    (f.prod g) ∘ₗ ℓ = α.prod β ↔ f ∘ₗ ℓ = α ∧ g ∘ₗ ℓ = β := by
  rw [prod_comp]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2]⟩
  · simpa using congrArg (fst R U V ∘ₗ ·) h
  · simpa using congrArg (snd R U V ∘ₗ ·) h

/-- Along a jointly injective span `U ← N → V`, two maps `α : E → U` and `β : E → V` have a
common lift to `N` exactly when every pair `(α e, β e)` lies in the joint range of the span; the
common lift is then unique. -/
theorem existsUnique_comp_eq_and_comp_eq_iff {f : N →ₗ[R] U} {g : N →ₗ[R] V}
    (hfg : Function.Injective (f.prod g)) {α : E →ₗ[R] U} {β : E →ₗ[R] V} :
    (∃! ℓ : E →ₗ[R] N, f ∘ₗ ℓ = α ∧ g ∘ₗ ℓ = β) ↔ ∀ e, (α e, β e) ∈ range (f.prod g) := by
  simp_rw [← prod_comp_eq_prod_iff]
  constructor
  · rintro ⟨ℓ, hℓ, -⟩ e
    exact ⟨ℓ e, by simpa using congr($hℓ e)⟩
  · intro h
    exact ⟨(α.prod β).codLift _ hfg fun e => h e, comp_codLift .., fun ℓ hℓ =>
      (cancel_left hfg).1 (hℓ.trans (comp_codLift ..).symm)⟩

end LinearMap
