/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Map
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Cutoff

/-!
# Coefficient comparisons between different ray cutoffs

A homogeneous coefficient map into a module supported at a smaller cutoff identifies
exactly the surviving source rays with the smaller ray fiber. This combines the
existing coefficient and enumeration-cutoff equivalences. Successive comparisons
compose on actual rays, even when either coefficient map kills decorations.

The comparison preserves complete degree-labelled encounter words, incoming tails,
paths and encounter parameters. No active wall is removed from the fixed geometric
alphabet. Thus an encounter whose label becomes the identity remains recorded.
The application to shifted BCH quotients uses their actual quotient transitions.

Whole-component coefficient comparisons follow Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2),
and Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

variable {R M N Γ V J K I : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] (d : PositiveDegrees Γ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Γ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 p)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)
  {k l : ℕ} (h : k ≤ l)
  (h𝓝 : ∀ q (x : N), x ∈ 𝓝 q → x ≠ 0 → q ∈ d.cutoff k) (Q : V)

local notation "a'" => regradeBase ℳ 𝓝 r (AddMonoidHom.id Γ) hr a
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C l Q
local notation "Target" => CutoffDecoratedRay d 𝓝 U a' v f c ε P W S C k Q

/-- Coefficient truncation identifies the surviving source fiber with the smaller
cutoff fiber. Only the target module must be supported in the smaller cutoff. -/
def cutoffDecoratedRayCoefficientTruncationEquiv :
    {β : Source // r β.decoration ≠ 0} ≃ Target :=
  (cutoffDecoratedRayCoefficientEquiv d ℳ 𝓝 r hr T U hT a v f c ε P W S C l Q).trans
    (cutoffDecoratedRayCutoffEquiv d 𝓝 U a' v f c ε P W S C h h𝓝 Q)

local notation "E" => cutoffDecoratedRayCoefficientTruncationEquiv d ℳ 𝓝 r hr T U hT a
  v f c ε P W S C h h𝓝 Q

/-- The complete degree-labelled encounter word is unchanged by truncation. -/
@[simp]
theorem cutoffDecoratedRayCoefficientTruncationEquiv_degreeItinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (E β).degreeItinerary = β.val.degreeItinerary := by
  simp only [cutoffDecoratedRayCoefficientTruncationEquiv, Equiv.trans_apply,
    cutoffDecoratedRayCutoffEquiv_degreeItinerary,
    cutoffDecoratedRayCoefficientEquiv_degreeItinerary]

/-- Truncation preserves the whole geometric path and hence its incoming tail. -/
@[simp]
theorem cutoffDecoratedRayCoefficientTruncationEquiv_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (E β).realization.2.ray = β.val.realization.2.ray := by
  simp only [cutoffDecoratedRayCoefficientTruncationEquiv, Equiv.trans_apply,
    cutoffDecoratedRayCutoffEquiv_ray, cutoffDecoratedRayCoefficientEquiv_ray]

/-- Truncation preserves every encounter time, including unchanged-degree encounters. -/
@[simp]
theorem cutoffDecoratedRayCoefficientTruncationEquiv_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (E β).realization.2.parameter β.val.realization.2.parameter := by
  rw [cutoffDecoratedRayCoefficientTruncationEquiv, Equiv.trans_apply]
  exact (cutoffDecoratedRayCutoffEquiv_parameter ..).trans
    (cutoffDecoratedRayCoefficientEquiv_parameter d ℳ 𝓝 r hr T U hT a
      v f c ε P W S C l Q β)

/-- The smaller ray carries the truncated whole final decoration. -/
@[simp↓]
theorem cutoffDecoratedRayCoefficientTruncationEquiv_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (E β).decoration = r β.val.decoration := by
  simp only [cutoffDecoratedRayCoefficientTruncationEquiv, Equiv.trans_apply,
    cutoffDecoratedRayCutoffEquiv_decoration, cutoffDecoratedRayCoefficientEquiv_decoration]

section Composition

variable {O : Type*} [AddCommMonoid O] [Module R O]
  (𝒪 : Γ → Submodule R O) [DirectSum.Decomposition 𝒪]
  (s : N →ₗ[R] O) (hs : ∀ p x, x ∈ 𝓝 p → s x ∈ 𝒪 p)
  (A : J → Module.End R O) (hU : ∀ j, s.comp (U j) = (A j).comp s)
  {j : ℕ} (hj : j ≤ k)
  (h𝒪 : ∀ q (x : O), x ∈ 𝒪 q → x ≠ 0 → q ∈ d.cutoff j)

/-- Successive coefficient truncations agree with their composite on every
surviving actual ray. Neither coefficient map is assumed injective. -/
theorem cutoffDecoratedRayCoefficientTruncationEquiv_comp
    (β : Source) (hb : s (r β.decoration) ≠ 0) :
    let β' := E ⟨β, fun hz => hb (by rw [hz, map_zero])⟩
    cutoffDecoratedRayCoefficientTruncationEquiv d 𝓝 𝒪 s hs U A hU a'
        v f c ε P W S C hj h𝒪 Q
        ⟨β', by rwa [cutoffDecoratedRayCoefficientTruncationEquiv_decoration]⟩ =
      cutoffDecoratedRayCoefficientTruncationEquiv d ℳ 𝒪 (s.comp r)
        (fun p x hx => hs p (r x) (hr p x hx)) T A
        (fun q => by rw [LinearMap.comp_assoc, hT q, ← LinearMap.comp_assoc,
          hU q, LinearMap.comp_assoc]) a v f c ε P W S C (hj.trans h) h𝒪 Q ⟨β, hb⟩ := by
  apply CutoffDecoratedRay.degreeItinerary_injective
  rw [cutoffDecoratedRayCoefficientTruncationEquiv_degreeItinerary,
    cutoffDecoratedRayCoefficientTruncationEquiv_degreeItinerary]
  exact (cutoffDecoratedRayCoefficientTruncationEquiv_degreeItinerary d ℳ 𝒪 (s.comp r)
    (fun p x hx => hs p (r x) (hr p x hx)) T A _ a v f c ε P W S C
    (hj.trans h) h𝒪 Q ⟨β, hb⟩).symm

end Composition

end Mei
